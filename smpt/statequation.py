"""
State Equation

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

from solver import Z3
from utils import STOP, Verdict, send_signal


class StateEquation:
    """
    State equation method.
    Check that the set of potentially reachable markings does not intersect any feared state. 
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False, solver_pids=None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Reduced Petri net
        self.ptnet_reduced = ptnet_reduced

        # System of linear equations
        self.system = system

        # Formula to study
        self.formula = formula

        # SMT solver
        self.solver = Z3(debug, solver_pids)

    def smtlib(self, k):
        """ SMT-LIB format for understanding.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction(k)
        else:
            smt_input = self.smtlib_with_reduction(k)

        smt_input += "(check-sat)\n(get-model)\n"

        return smt_input

    def smtlib_without_reduction(self, k):
        """ SMT-LIB format for understanding.
            Case without reduction.
        """
        smt_input = "" 

        smt_input += "; Declaration of the places from the Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the transitions from the Petri net\n"
        smt_input += self.ptnet.smtlib_declare_transitions()

        smt_input += "; State Equation\n"
        smt_input += self.ptnet.smtlib_state_equation()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        return smt_input

    def smtlib_with_reduction(self, k):
        """ SMT-LIB format for understanding.
            Case with reduction.
        """
        smt_input = "" 

        smt_input += "; Declaration of the places from the initial Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the variables and assert reduction equations\n"
        smt_input += self.system.smtlib()

        smt_input += "; Declaration of the transitions from the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_declare_transitions()

        smt_input += "; State Equation of the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_state_equation()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        return smt_input

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[STATE-EQUATION] RUNNING")

        if self.ptnet_reduced is None:
            prove = self.prove_without_reduction()
        else:
            prove = self.prove_with_reduction()

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if self.solver.aborted or prove is None:
            return

        # Put the result in the queue
        result.put([Verdict.INV, None])

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal(concurrent_pids.get(), STOP)

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri Net.
        """
        log.info("[STATE-EQUATION] > Declaration of the places from the Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())

        log.info("[STATE-EQUATION] > Declaration of the transitions from the Petri net")
        self.solver.write(self.ptnet.smtlib_declare_transitions())

        log.info("[STATE-EQUATION] > State Equation")
        self.solver.write(self.ptnet.smtlib_state_equation())

        log.info("[STATE-EQUATION] > Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        if not self.solver.check_sat():
            return False

        return None

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        log.info("[STATE-EQUATION] > Declaration of the places from the Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())

        log.info("[STATE-EQUATION] > Declaration of the variables and assert reduction equations")
        self.solver.write(self.system.smtlib())

        log.info("[STATE-EQUATION] > Declaration of the transitions from the Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_declare_transitions())

        log.info("[STATE-EQUATION] > State Equation")
        self.solver.write(self.ptnet_reduced.smtlib_state_equation())

        log.info("[STATE-EQUATION] > Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        if not self.solver.check_sat():
            return False

        return None

