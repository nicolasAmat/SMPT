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
__version__ = "4.0.0"

import logging as log
import sys
from multiprocessing import Queue
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.z3 import Z3
from smpt.ptio.formula import Formula
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
    formula_skeleton : Formula, optional
        Formula for skeleton.
    parikh : bool
        Generate Parikh vector.
    mcc : bool
        MCC mode.
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

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, ptnet_skeleton=None, formula_skeleton=None, mcc=False, debug=False, solver_pids=None, additional_techniques=None):
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

        # Skeleton and corresponding formula
        self.ptnet_skeleton: Optional[PetriNet] = ptnet_skeleton
        self.formula_skeleton: Optional[Formula] = formula_skeleton

        # Generate Parikh vector
        self.parikh = False

        # MCC mode
        self.mcc: bool = mcc

        # SMT solver
        self.solver: Z3 = Z3(debug=debug, solver_pids=solver_pids)
        self.debug: bool = debug
        self.solver_pids: Optional[Queue[int]] = solver_pids

        # Additional techniques queue
        self.additional_techniques: Optional[Queue[str]
                                             ] = additional_techniques

        # Trap constraints
        self.traps: Optional[TrapConstraints] = None

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
        log.info("[STATE-EQUATION] RUNNING")

        verdict = Verdict.UNKNOWN

        if self.ptnet_skeleton is not None:
            verdict = self.prove_without_reduction(skeleton=True)
            if verdict == Verdict.UNKNOWN:
                self.solver.reset()
            elif self.additional_techniques is not None:
                self.additional_techniques.put('SKELETON')

        if verdict == Verdict.UNKNOWN:
            if self.ptnet_reduced is None:
                verdict = self.prove_without_reduction()
            else:
                verdict = self.prove_with_reduction()

        if self.additional_techniques is not None:
            if self.ptnet.colored:
                self.additional_techniques.put('UNFOLDING_TO_PT')
            if self.ptnet_reduced is not None:
                self.additional_techniques.put('STRUCTURAL_REDUCTIONS')

        # Kill the solver
        self.solver.kill()
        if self.traps is not None:
            self.traps.solver.kill()

        # Quit if the solver has aborted, or if unknown result (and mcc mode disabled)
        if self.solver.aborted or (not self.mcc and verdict == Verdict.UNKNOWN):
            return

        # Put the result in the queue
        if verdict != Verdict.UNKNOWN:
            result.put((verdict, None))

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)

    def prove_without_reduction(self, skeleton: bool = False):
        """ Prover for non-reduced Petri Net.
        """
        ptnet: PetriNet =  self.ptnet_skeleton if skeleton else self.ptnet
        formula: Formula = self.formula_skeleton if skeleton else self.formula

        log.info("[STATE-EQUATION] > Declaration of the places from the Petri net")
        self.solver.write(ptnet.smtlib_declare_places())

        log.info("[STATE-EQUATION] > Declaration of the transitions from the Petri net")
        self.solver.write(ptnet.smtlib_declare_transitions(parikh=self.parikh and not skeleton))

        log.info("[STATE-EQUATION] > State Equation")
        self.solver.write(ptnet.smtlib_state_equation(parikh=self.parikh and not skeleton))

        log.info("[STATE-EQUATION] > Formula to check the satisfiability")
        self.solver.write(formula.R.smtlib(assertion=True))

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            return Verdict.INV
        elif self.parikh and not skeleton:
            parikh_set = self.solver.get_parikh(self.ptnet)
            with open(self.formula.parikh_filename, 'w') as fp:
                fp.write(' '.join(map(lambda tr: tr.id, parikh_set)))

        log.info("[STATE-EQUATION] > Add read arc constraints")
        self.solver.write(ptnet.smtlib_read_arc_constraints())

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        log.info("[STATE-EQUATION] > Add useful trap constraints")
        if self.trap_constraints(ptnet) is not None:
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            return Verdict.INV

        if ptnet.nupn is None or not ptnet.nupn.unit_safe or len(ptnet.nupn.units) > MAX_NUMBER_UNITS:
            log.info("[STATE-EQUATION] > Unknown")
            return Verdict.UNKNOWN

        sys.setrecursionlimit(10000)

        log.info("[STATE-EQUATION] > Add unit-safe local constraints")
        self.solver.write(ptnet.nupn.smtlib_local_constraints())

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
                self.additional_techniques.put('USE_NUPN')
            return Verdict.INV

        log.info("[STATE-EQUATION] > Add unit-safe hierarchical constraints")
        self.solver.write(ptnet.nupn.smtlib_hierarchy_constraints())

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
                self.additional_techniques.put('USE_NUPN')
            return Verdict.INV

        log.info("[STATE-EQUATION] > Unknown")
        return Verdict.UNKNOWN

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        log.info("[STATE-EQUATION] > Declaration of the places from the Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())

        log.info(
            "[STATE-EQUATION] > Declaration of the variables and assert reduction equations")
        self.solver.write(self.system.smtlib())

        log.info(
            "[STATE-EQUATION] > Declaration of the transitions from the Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_declare_transitions(parikh=self.parikh))

        log.info("[STATE-EQUATION] > State Equation")
        self.solver.write(self.ptnet_reduced.smtlib_state_equation(parikh=self.parikh))

        log.info("[STATE-EQUATION] > Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            return Verdict.INV
        elif self.parikh:
            parikh_set = self.solver.get_parikh(self.ptnet_reduced)
            with open(self.formula.parikh_filename, 'w') as fp:
                fp.write(' '.join(map(lambda tr: tr.id, parikh_set)))

        log.info("[STATE-EQUATION] > Add read arc constraints")
        self.solver.write(self.ptnet_reduced.smtlib_read_arc_constraints())

        log.info("[STATE-EQUATION] > Check satisfiability")
        if not self.solver.check_sat():
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        log.info("[STATE-EQUATION] > Add useful trap constraints")
        if self.trap_constraints(self.ptnet_reduced) is not None:
            if self.additional_techniques is not None:
                self.additional_techniques.put('TOPOLOGICAL')
            return Verdict.INV

        log.info("[STATE-EQUATION] > Unknown")
        return Verdict.UNKNOWN

    def trap_constraints(self, ptnet):
        """ Add useful trap constraints.
        """
        self.traps = TrapConstraints(
            ptnet, debug=self.debug, solver_pids=self.solver_pids)
        self.traps.assert_constraints()

        while True:

            # Compute useful trap
            trap = self.traps.get_trap(self.solver.get_marking(ptnet))

            if trap:
                # Assert trap constraints
                log.info("[STATE-EQUATION] > Assert a trap violating a witness")
                smt_input = ''.join(
                    map(lambda pl: "(> {} 0)".format(pl.id), trap))

                if len(trap) > 1:
                    smt_input = "(or {})".format(smt_input)

                self.solver.write("(assert {})\n".format(smt_input))

                log.info("[STATE-EQUATION] > Check satisfiability")
                if not self.solver.check_sat():
                    return False

            else:
                # Stop if no more useful trap constraints are found
                return None


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
