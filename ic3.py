#!/usr/bin/env python3

"""
IC3:
Incremental Construction of
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
__version__ = "2.0.0"

import copy
import logging as log
import os
import signal
import sys
from multiprocessing import Process, Queue

import psutil

from properties import Atom, Formula, IntegerConstant, StateFormula, TokenCount
from ptnet import PetriNet
from solver import Solver
from system import System


class Counterexample(Exception):
    """
    Exception raised in case of a counterexample.
    """


class IC3:
    """ 
    Incremental Construction of Inductive Clauses for Indubitable Correctness method.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False, unsat_core=True, parallelizer_pid=None):
        """ Initializer.

            By default the IC3 method uses the unsat core of the solver.
            Option to use the MIC algorithm: `unsat_core=False`.
        """
        self.ptnet = ptnet
        self.ptnet_reduced = ptnet_reduced

        self.system = system

        self.formula = formula

        self.reduction = ptnet_reduced is not None
        self.ptnet_current = self.ptnet_reduced if self.reduction else self.ptnet

        self.oars = []  # list of CNFs

        self.solver = Solver(debug)
        self.parallelizer_pid = parallelizer_pid
        
        if unsat_core:
            self.sub_clause_finder = self.sub_clause_finder_unsat_core
        else:
            self.sub_clause_finder = self.sub_clause_finder_mic


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

            Orders are equivalent to the declare places method.
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
        """ Assert F_i.
        """
        if i == 0:
            smt_input = self.oars[i][0].smtlib(0, assertion=True)
        else:
            smt_input = self.oars[i][0].smtlib(self.reduction * 10, assertion=True)

        for clause in self.oars[i][1:]:
            smt_input += clause.smtlib(0, assertion=True)

        return smt_input

    def oars_initialization(self):
        """ Initialization of the OARS.
            F0 = I and F1 = P.
        """
        log.info("[IC3] > F0 = I and F1 = P")

        # F0 = I
        equalities = []
        for pl in self.ptnet_current.places.values():
            equalities.append(Atom(TokenCount([pl]), IntegerConstant(pl.initial_marking), '='))
        self.oars.append([StateFormula(equalities, 'and')])

        # F1 = P
        self.oars.append([self.formula.P])

    def initial_marking_bad_state(self):
        """ sat (I and -P)
        """
        log.info("[IC3] > INIT => P")

        self.solver.write(self.declare_places(init=True))
        self.solver.write(self.assert_equations(init=True))
        self.solver.write(self.ptnet_current.smtlib_initial_marking(0))
        self.solver.write(self.formula.R.smtlib(self.reduction * 10, assertion=True))

        return self.solver.check_sat()

    def initial_marking_reach_bad_state(self):
        """ sat (I and T and -P')
        """
        log.info("[IC3] > INIT and T => P'")

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

    def state_reachable(self, i, s):
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
        """ sat (F_i and T and s')
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
        self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
        self.solver.write(s.smtlib(0, assertion=True, negation=True))
        self.solver.write(self.assert_equations())
        for eq in s.operands:
            self.solver.write("(assert (! {} :named {}))\n".format(eq.smtlib(1), eq.left_operand))

        # Read Unsatisfiable Core
        unsat_core = self.solver.get_unsat_core()

        inequalities = []
        for eq in s.operands:
            if str(eq.left_operand) in unsat_core:
                if eq.right_operand.value == 0:
                    inequalities.append(Atom(eq.left_operand, eq.right_operand, ">"))
                else:
                    inequalities.append(Atom(eq.left_operand, eq.right_operand, "<"))
        cl = StateFormula(inequalities, "or")

        log.info("[IC3] \t\t\t>> Clause learned: {}".format(cl))

        return cl

    def sub_clause_finder_mic(self, i, s):
        """ Minimal inductive clause (MIC).
        """
        c = copy.deepcopy(s)

        while len(c.operands) > 1:
            literal = c.operands.pop()

            self.solver.reset()

            self.solver.write(self.declare_places())
            self.solver.write(self.assert_formula(i))
            self.solver.write(self.ptnet_current.smtlib_transition_relation(0))
            self.solver.write(self.assert_equations())
            self.solver.write(c.smtlib(0, assertion=True, negation=True))
            self.solver.write(c.smtlib(1, assertion=True))

            if self.solver.check_sat():
                c.operands.append(literal)
                inequalities = []
                for eq in c.operands:
                    if int(eq.right_operand.value) == 0:
                        inequalities.append(Atom(eq.left_operand, eq.right_operand, "<"))
                cl = StateFormula(inequalities, "or")
                log.info("[IC3] \t\t\t>> Clause learned: {}".format(cl))
                return cl

        inequalities = []
        for eq in s.operands:
            inequalities.append(Atom(eq.left_operand, eq.right_operand, "<"))
        cl = StateFormula(inequalities, "or")

        log.info("[IC3] \t\t\t>> Clause learned: {}".format(cl))

        return cl

    def cube_filter(self, s):
        """ Extract a sub-cube with only non-null equalities,
            replace equalities by "greater or equal than".
        """
        non_zero = []
        for eq in s.operands:
            if eq.right_operand.value != 0:
                non_zero.append(Atom(eq.left_operand, eq.right_operand, ">="))

        return StateFormula(non_zero, "and")

    def prove(self, result=[]):
        """ Prover.
        """
        log.info("[IC3] RUNNING")

        if self.initial_marking_bad_state() or self.initial_marking_reach_bad_state():
            self.exit_helper(False, result)
            return False

        self.oars_initialization()

        k = 1

        while True:
            log.info("[IC3] > F{} = P".format(k + 1))

            self.oars.append([self.formula.P])
            if not self.strengthen(k):
                self.exit_helper(False, result)
                return False

            self.propagate_clauses(k)

            for i in range(1, k + 1):
                if set(self.oars[i]) == set(self.oars[i + 1]):
                    self.exit_helper(True, result)
                    return True

            k += 1

    def strengthen(self, k):
        """ Iterate until Fk excludes all states
            that lead to a dangerous state in one step.
        """
        log.info("[IC3] > Strengthen (k = {})".format(k))

        try:
            while self.formula_reach_bad_state(k):
                s = self.cube_filter(self.solver.get_model(self.ptnet_current, 0))
                n = self.inductively_generalize(s, k - 2, k)

                log.info("[IC3] \t\t>> s: {}".format(s))
                log.info("[IC3] \t\t>> n: {}".format(n))

                self.push_generalization([(n + 1, s)], k)
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
        log.info("[IC3] > Propagate Clauses (k = {})".format(k))

        for i in range(1, k + 1):
            for c in self.oars[i][1:]:  # we do not look at the first clause that corresponds to I or P
                if not self.formula_reach_clause(i, c) and c not in self.oars[i + 1]:
                    self.oars[i + 1].append(c)

    def inductively_generalize(self, s, minimum, k):
        """ Strengthen the invariants in F,
            by adding cubes generated during the `push_generalization`.
        """
        log.info("[IC3] \t> Inductively Generalize (s = {} min = {}, k = {})".format(s, minimum, k))

        if minimum < 0 and self.state_reachable(0, s):
            raise Counterexample

        for i in range(max(1, minimum + 1), k + 1):
            if self.state_reachable(i, s):
                self.generate_clause(s, i - 1, k)
                return i - 1

        self.generate_clause(s, k, k)

        return k

    def generate_clause(self, s, i, k):
        """ Find a minimal inductive cube `c` that is inductive relative to Fi.
            Add c to CL(Fi) for all 1 <= j <= i.
        """
        log.info("[IC3] \t\t\t> Generate Clause (i = {}, k = {})".format(i, k))

        c = self.sub_clause_finder(i, s)
        for j in range(1, i + 2):
            self.oars[j].append(c)

    def push_generalization(self, states, k):
        """ Apply inductive generalization of a dangerous state s 
            to its Fi state predecessors.
        """
        log.info("[IC3] \t> Push generalization (k = {})".format(k))

        while True:
            state = min(states, key=lambda t: t[0])
            n, s = state[0], state[1]

            if n > k:
                return

            if self.formula_reach_state(n, s):
                p = self.cube_filter(self.solver.get_model(self.ptnet_current, order=0))
                m = self.inductively_generalize(p, n - 2, k)
                states.append((m + 1, p))
            else:
                m = self.inductively_generalize(s, n, k)
                states.remove((n, s))
                states.append((m + 1, s))

    def exit_helper(self, result, result_output):
        """ Helper function to put the result to the output queue,
            and stop the concurrent method if there is one.
        """
        # Put the result in the queue
        result_output.put([result])

        # Kill parallelizer children
        if self.parallelizer_pid:
            ic3_pid = os.getpid()
            parent = psutil.Process(self.parallelizer_pid)
            children = parent.children(recursive=True)
            for process in children:
                if process.pid != ic3_pid:
                    try:
                        process.send_signal(signal.SIGTERM)
                    except psutil.NoSuchProcess:
                        pass

if __name__ == '__main__':

    if len(sys.argv) < 3:
        sys.exit("Argument missing: ./ic3.py <places_to_reach> <path_to_Petri_net> [<path_to_reduced_Petri_net>]")

    log.basicConfig(format="%(message)s", level=log.DEBUG)

    ptnet = PetriNet(sys.argv[2])

    marking = {ptnet.places[pl]: 1 for pl in sys.argv[1].split(',')}
    formula = Formula(ptnet)
    formula.generate_reachability(marking)

    if len(sys.argv) == 3:
        ptnet_reduced = None
        system = None
    else:
        ptnet_reduced = PetriNet(sys.argv[3])
        system = System(sys.argv[3], ptnet.places.keys(), ptnet_reduced.places.keys())

    ic3 = IC3(ptnet, formula, ptnet_reduced, system)

    print("> Result computed using z3")
    print("--------------------------")
    result = Queue()
    proc = Process(target=ic3.prove, args=(result,))
    proc.start()
    proc.join(timeout=60)
    if not result.empty():
        sat = not result.get()[0]
        print(formula.result(sat))
