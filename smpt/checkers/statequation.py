"""
State Equation Method

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
__version__ = "5.0"

from logging import info
from multiprocessing import Queue
from os import fsync
from sys import setrecursionlimit
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.certificate import certificate
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.z3 import Z3
from smpt.ptio.formula import Expression, Formula
from smpt.ptio.ptnet import PetriNet
from smpt.ptio.system import System
from smpt.ptio.verdict import Verdict

MAX_NUMBER_UNITS = 1000


class StateEquation(AbstractChecker):
    """ State equation method.
    
    Note
    ----
    Check that the set of potentially reachable markings does not intersect any feared state. 
   
    Attributes
    ----------
    ptnet : PetriNet
        Initial Petri net.
    ptnet_reduced : PetriNet, optional
        Reduced Petri net.
    system : System, optional
        System of reduction equations.
    formula : Formula
        Reachability formula.
    ptnet_skeleton : PetriNet, optional
        Skeleton of a colored Petri net.
    parikh : bool
        Generate Parikh vector.
    pre_run : bool
        Pre-run mode.
    solver : Z3
        SMT solver (Z3).
    debug : bool
        Debugging flag.
    solver_pids : Queue of int, optional
        Queue to share the current PID.
    additional_techniques : Queue of str, optional
        Queue to add some additional technique.
    traps : TrapConstraints, optional
        Engine to compute some trap constraints.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, ptnet_skeleton=None, formula_skeleton=None, pre_run=False, check_proof=False, path_proof= None, debug=False, solver_pids=None, additional_techniques=None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet: PetriNet = ptnet

        # Reduced Petri net
        self.ptnet_reduced: Optional[PetriNet] = ptnet_reduced

        # System of linear equations
        self.system: Optional[System] = system

        # Formula to study
        self.formula: Formula = formula

        # Skeleton Petri net
        self.ptnet_skeleton: Optional[PetriNet] = ptnet_skeleton
        self.formula_skeleton: Optional[Formula] = formula_skeleton

        # Generate Parikh vector
        self.parikh = formula.parikh_filename is not None

        # Pre-run mode
        self.pre_run: bool = pre_run

        # Proof checking options
        self.check_proof = check_proof
        self.path_proof = path_proof

        # SMT solver
        self.debug: bool = debug
        self.solver_pids: Optional[Queue[int]] = solver_pids
        self.solver: Optional[Z3] = None

        # Additional techniques queue
        self.additional_techniques: Optional[Queue[str]] = additional_techniques

        # Trap constraints
        self.traps: Optional[TrapConstraints] = None

        # Generated constraints
        self.read_arcs_are_used: bool = False
        self.used_traps: list[str] = []

    def smtlib(self):
        """ SMT-LIB format for understanding.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction()
        else:
            smt_input = self.smtlib_with_reduction()

        smt_input += "(check-sat)\n(get-model)\n"

        return smt_input

    def smtlib_without_reduction(self):
        """ SMT-LIB format for understanding.
            Case without reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the transitions from the Petri net\n"
        smt_input += self.ptnet.smtlib_declare_transitions(parikh=self.parikh)

        smt_input += "; State Equation\n"
        smt_input += self.ptnet.smtlib_state_equation()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        return smt_input

    def smtlib_with_reduction(self):
        """ SMT-LIB format for understanding.
            Case with reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the initial Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the variables and assert reduction equations\n"
        smt_input += self.system.smtlib()

        smt_input += "; Declaration of the transitions from the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_declare_transitions(parikh=self.parikh)

        smt_input += "; State Equation of the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_state_equation()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        return smt_input

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[STATE-EQUATION] RUNNING")
        self.solver =  Z3(debug=self.debug, solver_pids=self.solver_pids)

        verdict = Verdict.UNKNOWN

        if self.ptnet_skeleton is not None:
            verdict = self.prove_without_reduction(skeleton=True)
            if verdict == Verdict.UNKNOWN:
                self.solver.reset()
            elif self.additional_techniques is not None:
                self.additional_techniques.put('SKELETON')

        if self.ptnet is not None and verdict == Verdict.UNKNOWN:
            if self.ptnet_reduced is None:
                verdict = self.prove_without_reduction()
            else:
                verdict = self.prove_with_reduction()

            if verdict == Verdict.INV and (self.path_proof or self.check_proof):
                self.manage_poof()

        if self.additional_techniques is not None:
            if self.ptnet is not None:
                if self.ptnet.colored:
                    self.additional_techniques.put('UNFOLDING_TO_PT')
                if self.ptnet_reduced is not None:
                    self.additional_techniques.put('STRUCTURAL_REDUCTIONS')

        # Kill the solver
        self.solver.kill()
        if self.traps is not None:
            self.traps.solver.kill()

        # Quit if the solver has aborted, or if unknown result (and pre-run mode disabled)
        if self.solver.aborted or (not self.pre_run and verdict == Verdict.UNKNOWN):
            return

        # Put the result in the queue
        if verdict != Verdict.UNKNOWN:
            result.put((verdict, None))

        # Terminate concurrent methods
        send_signal_pids(concurrent_pids.get(), STOP)

    def prove_without_reduction(self, skeleton: bool = False):
        """ Prover for non-reduced Petri Net.
        """
        ptnet: PetriNet =  self.ptnet_skeleton if skeleton else self.ptnet
        R_current: Expression = self.formula_skeleton.R_skeleton if skeleton else self.formula.R

        info("[STATE-EQUATION] > Declaration of the places from the Petri net")
        self.solver.write(ptnet.smtlib_declare_places())

        info("[STATE-EQUATION] > Declaration of the transitions from the Petri net")
        self.solver.write(ptnet.smtlib_declare_transitions(parikh=self.parikh and not skeleton))

        info("[STATE-EQUATION] > State Equation")
        self.solver.write(ptnet.smtlib_state_equation(parikh=self.parikh and not skeleton))

        info("[STATE-EQUATION] > Formula to check the satisfiability")
        self.solver.write(R_current.smtlib(assertion=True))

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            return Verdict.INV

        info("[STATE-EQUATION] > Add read arc constraints")
        self.solver.write(ptnet.smtlib_read_arc_constraints(parikh=self.parikh and not skeleton))
        self.read_arcs_are_used = True

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV
        elif self.parikh and not skeleton:
            self.generate_parikh(ptnet)

        info("[STATE-EQUATION] > Add useful trap constraints")
        if self.trap_constraints(ptnet) is not None:
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            return Verdict.INV
        elif self.parikh and not skeleton:
            self.generate_parikh(ptnet)

        if ptnet.nupn is None or not ptnet.nupn.unit_safe or len(ptnet.nupn.units) > MAX_NUMBER_UNITS:
            info("[STATE-EQUATION] > Unknown")
            return Verdict.UNKNOWN

        setrecursionlimit(10000)

        info("[STATE-EQUATION] > Add unit-safe local constraints")
        self.solver.write(ptnet.nupn.smtlib_local_constraints())

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
                self.additional_techniques.put('USE_NUPN')
            return Verdict.INV

        info("[STATE-EQUATION] > Add unit-safe hierarchical constraints")
        self.solver.write(ptnet.nupn.smtlib_hierarchy_constraints())

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
                self.additional_techniques.put('USE_NUPN')
            return Verdict.INV

        info("[STATE-EQUATION] > Unknown")
        return Verdict.UNKNOWN

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        info("[STATE-EQUATION] > Declaration of the places from the Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())

        info("[STATE-EQUATION] > Declaration of the variables and assert reduction equations")
        self.solver.write(self.system.smtlib())

        info("[STATE-EQUATION] > Declaration of the transitions from the Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_declare_transitions(parikh=self.parikh))

        info("[STATE-EQUATION] > State Equation")
        self.solver.write(self.ptnet_reduced.smtlib_state_equation(parikh=self.parikh))

        info("[STATE-EQUATION] > Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            return Verdict.INV

        info("[STATE-EQUATION] > Add read arc constraints")
        self.solver.write(self.ptnet_reduced.smtlib_read_arc_constraints(parikh=self.parikh))
        self.read_arcs_are_used = True

        info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        info("[STATE-EQUATION] > Add useful trap constraints")
        if self.trap_constraints(self.ptnet_reduced) is not None:
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        info("[STATE-EQUATION] > Unknown")
        return Verdict.UNKNOWN

    def trap_constraints(self, ptnet):
        """ Add useful trap constraints.
        """
        self.traps = TrapConstraints(ptnet, debug=self.debug, solver_pids=self.solver_pids)
        self.traps.assert_constraints()

        while True:

            # Compute useful trap
            trap = self.traps.get_trap(self.solver.get_marking(ptnet))

            if trap:
                # Assert trap constraints
                info("[STATE-EQUATION] > Assert a trap violating a witness")
                smt_input = ''.join(map(lambda pl: "(> {} 0)".format(pl.id), trap))

                if len(trap) > 1:
                    smt_input = "(or {})".format(smt_input)

                if self.check_proof or self.path_proof:
                    self.used_traps.append(smt_input)

                self.solver.write("(assert {})\n".format(smt_input))

                info("[STATE-EQUATION] > Check satisfiability")
                if not self.solver.check_sat():
                    return False

            else:
                # Stop if no more useful trap constraints are found
                return None

    def generate_parikh(self, ptnet):
        """ Write a Parikh set from the state-equation.
        """
        parikh_set = self.solver.get_parikh(ptnet)
        with open(self.formula.parikh_filename, 'w') as fp:
            fp.write(' '.join(map(lambda tr: "{{{}}}".format(tr.id) if '-' in tr.id or '.' in tr.id else tr.id, parikh_set)))
            fsync(fp.fileno())

    def manage_poof(self) -> None:
        """ Manage certificate of invariance.
        """
        ptnet_current = self.ptnet_reduced if self.ptnet_reduced is not None else self.ptnet

        qf_cert = "(and {} {})".format(ptnet_current.smtlib_nonnegative_transitions(), ptnet_current.smtlib_state_equation(assertion=False))

        if self.read_arcs_are_used:
            constraints = ptnet_current.smtlib_read_arc_constraints(assertion=False)
            if constraints:
                qf_cert = "(and {} {})".format(qf_cert, constraints)

        if self.used_traps:
            qf_cert = "(and {} {})".format(qf_cert, ''.join(self.used_traps))

        cert = "(exists ({}) {})".format(ptnet_current.smtlib_declare_transitions_as_parameters(), qf_cert)

        if self.ptnet_reduced is not None:
            cert = "(exists ({}) (and {} {}))".format(self.system.smtlib_declare_additional_variables_as_parameters(), self.system.smtlib_as_one_formula(), cert)

        certificate(ptnet_current, self.formula, cert, path=self.path_proof, check=self.check_proof)

class TrapConstraints:
    """ Compute trap constraints.
    """

    def __init__(self, ptnet, debug=False, solver_pids=None):
        """ Initializer.
        """
        # Start new solver
        self.solver = Z3(debug=debug, solver_pids=solver_pids)

        # Current Petri net (can be reduced)
        self.ptnet = ptnet

    def assert_constraints(self):
        """ Assert trap constraints:
            - declaration,
            - trap is initially marked,
            - trap definition.
        """
        # Declare trap variables
        self.solver.write(self.ptnet.smtlib_declare_trap())

        # Assert that places in the trap are initially marked
        self.solver.write(self.ptnet.smtlib_trap_initially_marked())

        # Trap definition
        self.solver.write(self.ptnet.smtlib_trap_definition())

    def get_trap(self, marking):
        """ Get a trap violating the marking if there is one,
            by only considering unmarked places in our candidate.
        """
        # Push
        self.solver.push()

        # Consider unmarked places in our candidate
        self.solver.write(marking.smtlib_consider_unmarked_places_for_trap())

        # Get trap if there is one
        trap = []
        if self.solver.check_sat():
            trap = self.solver.get_trap(self.ptnet)

        # Pop
        self.solver.pop()
        return trap
