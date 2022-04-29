"""
PDR - Incremental Construction of
Inductive Clauses for Indubitable Correctness

Based on "SAT-Based Model Checking without Unrolling"
Aaron Bradley, VMCAI 2011
Adapted for Petri nets

Orders (state' denotes a state reached by firing one transition):
- Case non-reduced:
    ptnet : 0
    ptnet': 1
- Case reduced:
    ptnet : 10     ptnet_reduced : 0
    ptnet': 11     ptnet_reduced': 1   

NB: PDR-REACH and PDR-REACH-SATURATED are not currently compatible with the use of reductions.

This file is part of SMPT.

SMPT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

SMPT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with SMPT. If not, see <https://www.gnu.org/licenses/>.
"""

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import copy
import logging as log
import resource

from formula import (ArithmeticOperation, Atom, FreeVariable, IntegerConstant,
                     StateFormula, TokenCount, UniversalQuantification)
from solver import Z3
from utils import STOP, Verdict, send_signal_pids


class Counterexample(Exception):
    """
    Exception raised in case of a counterexample.
    """


class States:
    """
    Set of states represented by:
    - a cube,
    - an hurdle and delta vector,
    - saturated hurdle and delta vectors if saturation enabled.
    """

    def __init__(self, cube, saturation=False):
        """ Initializer.
        """
        # Reached cube
        self.cube = cube

        # Saturation enabling
        self.saturation = saturation

        # Standard hurdle and delta vectors
        self.delta = {}
        self.hurdle = {}

        # Special data-structure for transition saturation
        if saturation:
            # Saturation variables (free-variables)
            self.saturation_vars = []

            # Current hurdle and delta vectors
            self.current_hurdle = {}
            self.current_delta = {}

            # Saturated hurdle and delta vectors 
            self.saturated_hurdle = []
            self.saturated_delta = {}

            # Composed hurdle and delta vectors
            self.composed_hurdle = []
            self.composed_delta = {}

    def __str__(self):
        """ States to textual format.
            (debugging function)
        """
        if self.saturation:
            return " and ".join(["({} >= {})".format(pl.id, hurdle) for pl, hurdle in self.compose_hurdle()] + [str(self.cube.generalize(saturated_delta=self.compose_delta()))])
        else:
            return  " and ".join(["({} >= {})".format(pl.id, hurdle) for pl, hurdle in self.hurdle.items()] + [str(self.cube.generalize(self.delta))])

    def smtlib(self, k=None, assertion=False, negation=False):
        """ States to SMT-LIB format.
        """
        declaration, smt_input = "", ""

        if self.saturation and self.saturation_vars:
            # p >= H(\sigma)
            smt_input += ' '.join(["(>= {} {})".format(pl.smtlib(k), hurdle.smtlib(k)) for pl, hurdle in self.compose_hurdle()])

            # c{p <- p - \Delta(\sigma)}
            smt_input += self.cube.smtlib(k, saturated_delta=self.compose_delta())

            # Conjunction of the conditions
            smt_input = "(and {})".format(smt_input)

            if negation:
                # Declaration of the saturation variables
                quantified_variables = ' '.join(map(lambda var: "({} Int)".format(var.smtlib(k)), self.saturation_vars))
                # Universal quantification
                smt_input = "(forall ({}) (not {}))".format(quantified_variables, smt_input)
            else:
                # Declaration of the saturation variables
                declaration = ''.join(map(lambda var: var.smtlib_declare(k), self.saturation_vars))

        else:
            # p >= H(\sigma)
            for pl, hurdle in self.hurdle.items():
                smt_input += "(>= {} {})".format(pl.smtlib(k), hurdle)

            # c{p <- p - \Delta(\sigma)}
            smt_input += self.cube.smtlib(k, delta=self.delta)

            # Conjunction of the conditions
            smt_input = "(and {})".format(smt_input)

            # Optional negation
            if negation:
                smt_input = "(not {})".format(smt_input)

        # Optional assertion
        if assertion:
            smt_input = "(assert {})\n".format(smt_input)

        return declaration + smt_input

    def step_back(self, tr):
        """ Return previous states from a given transition.
        """
        # Create a new States object
        prev_states = States(self.cube, self.saturation)

        # Update the standard hurdle and delta vectors

        # H(t.\sigma) = max(H(t), H(\sigma) - \Delta(t))
        prev_states.hurdle = {pl: max(tr.pre.get(pl, 0), self.hurdle.get(pl, 0) - tr.delta.get(pl, 0)) for pl in set(tr.pre) |set(self.hurdle)}
        prev_states.hurdle = {pl: hurdle for pl, hurdle in prev_states.hurdle.items() if hurdle != 0}

        # \Delta(t.\sigma) = \Delta(t) + \Delta(\sigma)
        prev_states.delta = {pl: self.delta.get(pl, 0) + tr.delta.get(pl, 0) for pl in set(self.delta) | set(tr.delta)}

        # If saturation is enabled, update the saturated hurdle and delta vectors
        if self.saturation:
            # Copy saturation variables
            prev_states.saturation_vars = self.saturation_vars[:]

            # H(t.\sigma) = max(H(t), H(\sigma) - \Delta(t))
            prev_states.current_hurdle = {pl: max(tr.pre.get(pl, 0), self.current_hurdle.get(pl, 0) - tr.delta.get(pl, 0)) for pl in set(tr.pre) | set(self.current_hurdle)}
            prev_states.current_hurdle = {pl: hurdle for pl, hurdle in prev_states.current_hurdle.items() if hurdle != 0}

            # \Delta(t.\sigma) = \Delta(t) + \Delta(\sigma)
            prev_states.current_delta = {pl: self.current_delta.get(pl, 0) + tr.delta.get(pl, 0) for pl in set(self.current_delta) | set(tr.delta)}

            # Copy saturated hurdle and delta vectors
            prev_states.saturated_hurdle = [{pl: copy.copy(hurdle) for pl, hurdle in saturated_hurdle.items()} for saturated_hurdle in self.saturated_hurdle] 
            prev_states.saturated_delta = {pl: copy.copy(delta) for pl, delta in self.saturated_delta.items()}

            # Check if saturation is needed
            if prev_states.cube.need_saturation(prev_states.current_delta) or all(prev_states.current_delta.get(pl, 0) >= 0 for hurdle in self.saturated_hurdle for pl in hurdle):
                prev_states.sature_current_sequence()

        return prev_states

    def sature_current_sequence(self):
        """ Sature the current sequence.
        """
        # Generate a new saturation variable
        saturation_var = FreeVariable("PDR_{}".format(id(self)), len(self.saturation_vars) + 1)
        self.saturation_vars += [saturation_var]

        # p >= H(t^{k+1}.\sigma) \equiv p >= H(t^{k+1}) /\ p >= H(\sigma) - \Delta(t^{k+1})
        for saturated_sequence_hurdle in self.saturated_hurdle:
            for pl in saturated_sequence_hurdle:
                if pl in self.current_delta:
                    saturated_sequence_hurdle[pl].append(ArithmeticOperation([IntegerConstant(-self.current_delta[pl]), ArithmeticOperation([saturation_var, IntegerConstant(1)], '+')], '*'))

        # H(t^{k+1})_j = H(t)_j + k * \Delta(t)_j if \Delta(t)_j < 0 else H(t)_j
        saturated_hurdle = {}
        for pl, hurdle in self.current_hurdle.items():
            delta = self.current_delta.get(pl, 0)
            if delta < 0 :
                saturated_hurdle[pl] = [IntegerConstant(hurdle), ArithmeticOperation([saturation_var, IntegerConstant(-delta)], '*')]
            else:
                saturated_hurdle[pl] = [IntegerConstant(hurdle)]

        self.saturated_hurdle.append(saturated_hurdle)

        # \Delta(t^{k+1}.\sigma) = \Delta(t^{k+1}) + \Delta(\sigma) = (k + 1) * \Delta(t) + \Delta(\sigma)
        self.saturated_delta = {pl: self.saturated_delta.get(pl, []) + [ArithmeticOperation([IntegerConstant(self.current_delta[pl]), ArithmeticOperation([saturation_var, IntegerConstant(1)], '+')], '*')] if pl in self.current_delta else self.saturated_delta[pl] for pl in set(self.saturated_delta) | set(self.current_delta)}

        # Clean the current hurdle and delta vectors
        self.current_hurdle, self.current_delta = {}, {}

    def compose_hurdle(self):
        """ Compose the current and saturated hurdles.
        """
        if not self.composed_hurdle:
            # p >= H(\sigma.\sigma') \equiv p >= H(\sigma) /\ p >= H(\sigma') - \Delta(\sigma)

            # Current hurdle
            # p >= H(\sigma)
            hurdles = [(pl, IntegerConstant(hurdle)) for pl, hurdle in self.current_hurdle.items()]

            # Saturated hurdle
            # p >= H(\sigma') - \Delta(\sigma)
            for hurdle in self.saturated_hurdle:
                for pl, constraint_sum in hurdle.items():
                    lower_bound = constraint_sum + [IntegerConstant(- self.current_delta[pl])] if self.current_delta.get(pl, 0) else constraint_sum
                    lower_bound = ArithmeticOperation(lower_bound, '+') if len(lower_bound) > 1 else lower_bound[0]
                    hurdles.append((pl, lower_bound))

            self.composed_hurdle = hurdles
            
        return self.composed_hurdle

    def compose_delta(self):
        """ Compose the current and saturated deltas.
        """
        if not self.composed_delta:
            # \Delta(\sigma.\sigma') = \Delta(\sigma) + \Delta(\sigma')
            self.composed_delta = {pl: [IntegerConstant(self.current_delta[pl])] + self.saturated_delta.get(pl, []) if pl in self.current_delta else self.saturated_delta[pl] for pl in set(self.current_delta) | set(self.saturated_delta)}

        return self.composed_delta

    def smtlib_unsat_core(self, k):
        """ Generated the SMT-LIB output to obtain an unsat core.
        """
        smtlib_input = ""

        if self.saturation:
            # Declaration of the saturation variables
            smtlib_input += ''.join(map(lambda var: var.smtlib_declare(k), self.saturation_vars))
            
            # Assert hurdles with clause names corresponding to indices
            for index, (pl, hurdle) in enumerate(self.compose_hurdle()):
                smtlib_input += "(assert (! (>= {} {}) :named lit@H{}))\n".format(pl.smtlib(k), hurdle.smtlib(k), index)

            smtlib_input += self.cube.smtlib_unsat_core(k, saturated_delta=self.compose_delta())

        else:
            # Assert hurdles with clause names corresponding to ids
            for pl, hurdle in self.hurdle.items():
                smtlib_input += "(assert (! (>= {} {}) :named lit@H{}))\n".format(pl.smtlib(k), hurdle, pl.id)

            # Assert cube with clause names
            smtlib_input += self.cube.smtlib_unsat_core(k, delta=self.delta)

        return smtlib_input

    def learned_clause_from_unsat_core(self, ptnet, unsat_core):
        """ Return a clause corresponding to a given unsat core.
        """
        literals = []

        if self.saturation:

            if unsat_core != ['All']:
                # Case unsat core engine dit not give up
                # Get core of hurdles
                for literal in filter(lambda literal: 'lit@H' in literal, unsat_core):
                    index = int(literal.split('@H')[1])
                    place = self.compose_hurdle()[index][0]
                    hurdle = self.compose_hurdle()[index][1]
                    literals.append(Atom(TokenCount([place]), hurdle, '<'))

                unsat_literals = list(filter(lambda lit: 'lit@c' in lit, unsat_core))
            else:
                # Case unsat core engine gave up
                # Use all hurdles
                for place, hurdle in self.compose_hurdle():
                    literals.append(Atom(TokenCount([place]), hurdle, '<'))

                unsat_literals = unsat_core

            # Get core of the feared cube
            literals += self.cube.learned_clauses_from_unsat_core(unsat_literals, saturated_delta=self.compose_delta())

            # Construct the corresponding clause
            if self.saturated_hurdle:
                literals.extend([Atom(var, IntegerConstant(0), '<') for var in self.saturation_vars])
                clause = UniversalQuantification(self.saturation_vars[:], StateFormula(literals, 'or'))
            else:
                clause = StateFormula(literals, 'or')

        else:
            # Get core of hurdles
            for literal in filter(lambda literal: 'lit@H' in literal, unsat_core):
                place = ptnet.places[literal.split('@H')[1]]
                literals.append(Atom(TokenCount([place]), IntegerConstant(self.hurdle[place]), '<'))

            # Get core of the feared cube
            literals += self.cube.learned_clauses_from_unsat_core(list(filter(lambda lit: 'lit@c' in lit, unsat_core)), delta=self.delta)

            # Construct the corresponding clause
            clause = StateFormula(literals, "or")

        log.info("[PDR] \t\t\t>> Clause learned: {}".format(clause))
        return clause


class PDR:
    """ 
    Incremental Construction of Inductive Clauses for Indubitable Correctness method.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False,  check_proof=False, method='REACH', saturation=False, unsat_core=True, solver_pids=None):
        """ Initializer.

            By default the PDR method uses the unsat core of the solver.
            Option to use the MIC algorithm: `unsat_core=False`.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Reduced Petri net
        self.ptnet_reduced = ptnet_reduced

        # System of linear equations
        self.system = system

        # Formula to study
        self.formula = formula

        # Use of reductions
        self.reduction = ptnet_reduced is not None

        # Petri net to unfold
        self.ptnet_current = self.ptnet_reduced if self.reduction else self.ptnet

        # Over Approximated Reachability Sequences (OARS) - list of CNFs
        self.oars = []

        # Feared states
        self.feared_states = []

        # SMT solver
        self.solver = Z3(debug=debug, solver_pids=solver_pids)

        # Used method to obtain minimal inductive cubes
        if unsat_core:
            self.sub_clause_finder = self.sub_clause_finder_unsat_core
        else:
            self.sub_clause_finder = self.sub_clause_finder_mic

        # Proof checking option
        self.check_proof = check_proof

        # Set method: `COV` or `REACH`
        self.method = method

        # Saturation for the transition-based generalization
        self.saturation = saturation

    def declare_places(self, init=False):
        """ Declare places.

            Without reductions:
            If init is True:  declare places at order 0,
            If init is False: declare places at order 0 and 1.

            With reductions:
            If init is True:  declare initial places at order 10, reduced places at order 0.
            If init is False: declare initial places at order 10 and 11, reduced places at order 0 and 1.
        """
        if init:
            if self.reduction:
                return self.ptnet.smtlib_declare_places(10) \
                       + self.ptnet_reduced.smtlib_declare_places(0)
            else:
                return self.ptnet.smtlib_declare_places(0)
        else:
            if self.reduction:
                return self.ptnet.smtlib_declare_places(10) \
                       + self.ptnet.smtlib_declare_places(11) \
                       + self.ptnet_reduced.smtlib_declare_places(0) \
                       + self.ptnet_reduced.smtlib_declare_places(1)
            else:
                return self.ptnet.smtlib_declare_places(0) \
                       + self.ptnet.smtlib_declare_places(1)

    def assert_equations(self, init=False):
        """ Assert reduction equations.

            Orders are equivalent to the `declare_places` method.
        """
        if not self.reduction:
            return ""

        if init:
            return self.system.smtlib_declare_additional_variables(10) \
                   + self.system.smtlib_equations_without_places_from_reduced_net(10) \
                   + self.system.smtlib_equations_with_places_from_reduced_net(0, 10) \
                   + self.system.smtlib_link_nets(0, 10)
        else:
            return self.system.smtlib_declare_additional_variables(10) \
                   + self.system.smtlib_equations_without_places_from_reduced_net(10) \
                   + self.system.smtlib_equations_with_places_from_reduced_net(0, 10) \
                   + self.system.smtlib_link_nets(0, 10) \
                   + self.system.smtlib_declare_additional_variables(11) \
                   + self.system.smtlib_equations_without_places_from_reduced_net(11) \
                   + self.system.smtlib_equations_with_places_from_reduced_net(1, 11) \
                   + self.system.smtlib_link_nets(1, 11)

    def assert_formula(self, i):
        """ Assert Fi.
        """
        if i == 0:
            smt_input = self.oars[i][0].smtlib(0, assertion=True)
        else:
            smt_input = self.oars[i][0].smtlib(self.reduction * 10, assertion=True)

        for clause in self.oars[i][1:]:
            smt_input += clause.smtlib(0, assertion=True)

        return smt_input

    def assert_negation_formula(self, i, k=0):
        """ Assert -Fi.
        """
        return "(assert (or {}))".format(''.join(map(lambda clause: clause.smtlib(k, negation=True), self.oars[i])))

    def oars_initialization(self):
        """ Initialization of the OARS.
            F0 = I and F1 = P.
        """
        log.info("[PDR] > F0 = I and F1 = P")

        # F0 = I
        marking = []
        for pl in self.ptnet_current.places.values():
            marking.append(Atom(TokenCount([pl]), IntegerConstant(pl.initial_marking), '='))
        self.oars.append([StateFormula(marking, 'and')])

        # F1 = P
        self.oars.append([self.formula.P])

        # Get feared states
        if self.method == 'REACH':
            if isinstance(self.formula.R, StateFormula):
                self.feared_states = [States(cube, self.saturation) for cube in self.formula.R.get_cubes()]

    def initial_marking_reach_bad_state(self):
        """ sat (I and T and -P')
        """
        log.info("[PDR] > INIT and T => P'")

        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.ptnet_current.smtlib_initial_marking(0))
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(self.assert_equations())
        self.solver.write(self.formula.R.smtlib(self.reduction * 10 + 1, assertion=True))

        return self.solver.check_sat()

    def formula_reach_bad_state(self, k):
        """ sat (Fk and T and -P')
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(k))
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(self.assert_equations())
        self.solver.write(self.formula.R.smtlib(self.reduction * 10 + 1, assertion=True))

        return self.solver.check_sat()

    def formula_reach_clause(self, i, c):
        """ sat (Fi and T and -c')
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(c.smtlib(1, assertion=True, negation=True))

        return self.solver.check_sat()

    def clause_not_relative_inductive(self, i, s):
        """ sat (-s and Fi and T and s')
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(s.smtlib(0, assertion=True, negation=True))
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(self.assert_equations())
        self.solver.write(s.smtlib(1, assertion=True))

        return self.solver.check_sat()

    def formula_reach_state(self, i, s):
        """ sat (Fi and T and s')
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(self.assert_equations())
        self.solver.write(s.smtlib(k=1, assertion=True))

        return self.solver.check_sat()

    def sub_clause_finder_unsat_core(self, i, s):
        """ unsat core (-s and Fi and T and s')
        """
        self.solver.reset()
        self.solver.enable_unsat_core()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.ptnet.smtlib_transition_relation(0))
        self.solver.write(s.smtlib(0, assertion=True, negation=True))

        self.solver.write(s.smtlib_unsat_core(1))
        unsat_core = self.solver.get_unsat_core()

        return s.learned_clause_from_unsat_core(self.ptnet, unsat_core)

    def sub_clause_finder_mic(self, i, s):
        """ Minimal inductive clause (MIC).
        """
        raise NotImplementedError

    def unsat_cubes_removal(self):
        """ Remove unsat cubes in R.
            If no cubes are satisfiable return True.
        """
        log.info("[PDR] > Remove unsat cubes from R")

        self.solver.reset()

        self.solver.write(self.ptnet.smtlib_declare_places())
        
        sat_cubes = []
        for cube in self.formula.R.get_cubes():
            # Add only sat cubes
            self.solver.push()
            self.solver.write(cube.smtlib(assertion=True))
            if self.solver.check_sat():
                sat_cubes.append(cube)
                self.solver.pop()

        # If no sat cubes, formula `P` is an invariant
        if not sat_cubes:
            return True

        # Reconstruct formulas
        self.formula.R.operands = sat_cubes
        self.formula.P = StateFormula([self.formula.R], 'not')

        # Obtain feared states    
        self.feared_states = [States(cube, self.saturation) for cube in sat_cubes]
     
        return False

    def fixed_point(self, i):
        """ Check if Fi is a fixed point.
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_negation_formula(i, 0))
        self.solver.write(self.assert_formula(i + 1))

        return not self.solver.check_sat()

    def witness_generalizer(self, states):
        """ Generalize a witness.
            - `REACH`: block the fired transition,
            - `COV`: extract a sub-cube with only non-null equalities,
            replace equalities by "greater or equal than".
        """
        log.info("[PDR] \t>> Generalization (s = {})".format(' or '.join(map(str, states))))

        if self.method == 'REACH':
            # Get a marking sequence m_1 -> m_2
            m_1, m_2 = self.solver.get_step(self.ptnet_current)

            # Get the corresponding reached cube
            if len(states) > 1:
                s = next(filter(lambda s: s.cube.eval(m_2), states), None)
            else:
                s = states[0]

            # Get the corresponding fired transition
            tr = self.ptnet_current.get_transition_from_step(m_1, m_2)

            # Return the generalized reached cube according the fired transition
            generalization = s.step_back(tr)

        else:
            # Get a witness marking
            s = self.solver.get_marking(self.ptnet_current, order=0)

            # Construct the generalization cube
            literals = []
            for place, tokens in s.tokens.items():
                if tokens:
                    literals.append(Atom(TokenCount([place]), IntegerConstant(tokens), ">="))
            generalization = States(StateFormula(literals, "and"))

        log.info("[PDR] \t   {}".format(generalization))
        return generalization

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[PDR] RUNNING")

        if self.initial_marking_reach_bad_state():
            self.exit_helper(Verdict.CEX, result, concurrent_pids)
            return Verdict.CEX

        if self.method == 'REACH':
            # Limit the memory of the current thread to 4Go (due to the DNF transform explosion)
            resource.setrlimit(resource.RLIMIT_AS, (4294967296, 4294967296))

            # Transform R into DNF
            try:
                self.formula = self.formula.dnf()
            except MemoryError:
                self.solver.kill()
                return

            # Remove UNSAT cubes, and exit if R UNSAT
            if self.unsat_cubes_removal():
                self.exit_helper(Verdict.INV, result, concurrent_pids)
                return Verdict.INV

        log.info("[PDR] > R = {}".format(self.formula.R))
        log.info("[PDR] > P = {}".format(self.formula.P))

        self.oars_initialization()

        k = 1

        while True:
            log.info("[PDR] > F{} = P".format(k + 1))

            self.oars.append([self.formula.P])
            if not self.strengthen(k):
                self.exit_helper(Verdict.CEX, result, concurrent_pids)
                return Verdict.CEX

            self.propagate_clauses(k)

            for i in range(1, k + 1):
                if (not self.saturation and set(self.oars[i]) == set(self.oars[i + 1])) or (self.saturation and self.fixed_point(i)):
                    if self.check_proof:
                        self.proof_checking(i)
                    self.exit_helper(Verdict.INV, result, concurrent_pids)
                    return Verdict.INV

            k += 1

    def strengthen(self, k):
        """ Iterate until Fk excludes all states
            that lead to a dangerous state in one step.
        """
        log.info("[PDR] > Strengthen (k = {})".format(k))

        try:
            while self.formula_reach_bad_state(k):
                s = self.witness_generalizer(self.feared_states)
                n = self.inductively_generalize(s, k - 2, k)

                log.info("[PDR] \t\t>> s: {}".format(s))
                log.info("[PDR] \t\t>> n: {}".format(n))

                self.push_generalization({(n + 1, s)}, k)
            return True

        except Counterexample:
            return False

    def propagate_clauses(self, k):
        """ For 1 <= i <= k,
            look at a clause c in CL(Fi) and not in CL(Fi+1),
            s.t. unsat (Fi and T and -c').
            When this is the case, propagate the clause forward,
            i.e. add c to CL(Fi+1)
        """
        log.info("[PDR] > Propagate Clauses (k = {})".format(k))

        for i in range(1, k + 1):
            for c in self.oars[i][1:]:  # we do not look at the first clause that corresponds to I or P
                if not self.formula_reach_clause(i, c) and c not in self.oars[i + 1]:
                    self.oars[i + 1].append(c)

    def inductively_generalize(self, s, minimum, k):
        """ Strengthen the invariants in F,
            by adding cubes generated during the `push_generalization`.
        """
        log.info("[PDR] > Inductively Generalize (s = {} min = {}, k = {})".format(s, minimum, k))

        if minimum < 0 and self.formula_reach_state(0, s):
            raise Counterexample

        for i in range(max(1, minimum + 1), k + 1):
            if self.clause_not_relative_inductive(i, s):
                log.info('[PDR] \t>> F{} reach {}'.format(i, s))
                self.generate_clause(s, i - 1, k)
                return i - 1

        self.generate_clause(s, k, k)
        return k

    def generate_clause(self, s, i, k):
        """ Find a minimal inductive cube `c` that is inductive relative to Fi.
            Add c to CL(Fi) for all 1 <= j <= i.
        """
        log.info("[PDR] > Generate Clause (i = {}, k = {})".format(i, k))

        c = self.sub_clause_finder(i, s)

        for j in range(1, i + 2):
            self.oars[j].append(c)

    def push_generalization(self, states, k):
        """ Apply inductive generalization of a dangerous state s 
            to its Fi state predecessors.
        """
        log.info("[PDR] > Push generalization (k = {})".format(k))

        while True:
            n, s = min(states, key=lambda t: t[0])

            if n > k:
                return

            if self.formula_reach_state(n, s):
                log.info('[PDR] \t>> F{} reach {}'.format(n, s))
                p = self.witness_generalizer([s])
                m = self.inductively_generalize(p, n - 2, k)
                states.add((m + 1, p))
            else:
                m = self.inductively_generalize(s, n, k)
                states.remove((n, s))
                states.add((m + 1, s))

    def proof_checking(self, i):
        """ Check the certificate of invariance.
        """
        print("################################")
        print("[PDR] Certificate of invariance")
        print('\n'.join(map(lambda clause: "# " + str(clause), self.oars[i])))
        print("################################")

        print("[PDR] Certificate checking")

        self.solver.reset()
        self.solver.write(self.declare_places(0))
        self.solver.write(self.oars[0][0].smtlib(k=0, assertion=True))
        self.solver.write(self.assert_negation_formula(i))
        print("# UNSAT(I /\ -Proof):", not self.solver.check_sat())

        self.solver.reset()
        self.solver.write(self.declare_places(0))
        self.solver.write(self.formula.R.smtlib(k=0, assertion=True))
        self.solver.write(self.assert_formula(i))
        print("# UNSAT(R /\ Proof):", not self.solver.check_sat())

        self.solver.reset()
        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(self.assert_negation_formula(i, 1))
        print("# UNSAT(Proof /\ T /\ -Proof'):", not self.solver.check_sat())

        print("################################")

    def exit_helper(self, verdict, result_output, concurrent_pids):
        """ Helper function to put the result to the output queue,
            and stop the concurrent method if there is one.
        """
        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if self.solver.aborted:
            return

        # Put the result in the queue
        result_output.put([verdict, None])

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)

