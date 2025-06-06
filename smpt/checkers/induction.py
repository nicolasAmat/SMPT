# I need to implement the certificate generation here!
"""
Induction

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
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.certificate import certificate
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.z3 import Z3
from smpt.ptio.verdict import Verdict


class Induction(AbstractChecker):
    """
    Induction method.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, show_model=False, check_proof=False, path_proof=None, debug=False, solver_pids=None):
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

        # Show model option
        self.show_model = show_model

        # Proof checking options
        self.check_proof = check_proof
        self.path_proof = path_proof

        # SMT solver
        self.debug = debug
        self.solver_pids = solver_pids
        self.solver: Optional[Z3] = None

    def smtlib(self):
        """ SMT-LIB format for debugging.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction()
        else:
            smt_input = self.smtlib_with_reduction()

        return smt_input

    def smtlib_without_reduction(self):
        """ SMT-LIB format for debugging.
            Case without reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net (0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Push\n"
        smt_input += "(push)\n"

        smt_input += "; Initial marking of the Petri net\n"
        smt_input += self.ptnet.smtlib_initial_marking(0)

        smt_input += "; Assert feared safes (0)\n"
        smt_input += self.formula.R.smtlib(0, assertion=True)

        smt_input += "; Check satisfiability\n"
        smt_input += "(check-sat)\n"

        smt_input += "; Pop\n"
        smt_input += "(pop)\n"

        smt_input += "; Declaration of the places from the Petri net (0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Assert states safes (0)\n"
        smt_input += self.formula.P.smtlib(0, assertion=True)

        smt_input += "; Declaration of the places from the Petri net (1)\n"
        smt_input += self.ptnet.smtlib_declare_places(1)

        smt_input += "; Transition relation: 0 -> 1\n"
        smt_input += self.ptnet.smtlib_transition_relation(0, eq=False)

        smt_input += "; Formula to check the satisfiability (1)\n"
        smt_input += self.formula.R.smtlib(1, assertion=True)

        smt_input += "; Check satisfiability\n"
        smt_input += "(check-sat)\n"

        return smt_input

    def smtlib_with_reduction(self, k):
        """ SMT-LIB format for debugging.
            Case with reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net (0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Assert reduction equations"
        smt_input += self.system.smtlib(0, 0)

        smt_input += "; Push\n"
        smt_input += "(push)\n"

        smt_input += "; Initial marking of the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_initial_marking(0)

        smt_input += "; Assert feared safes (0)\n"
        smt_input += self.formula.R.smtlib(0, assertion=True)

        smt_input += "; Check satisfiability\n"
        smt_input += "(check-sat)\n"

        smt_input += "; Pop\n"
        smt_input += "(pop)\n"

        smt_input += "; Declaration of the places from the Petri net (0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Assert states safes (0)\n"
        smt_input += self.formula.P.smtlib(0, assertion=True)

        smt_input += "; Declaration of the places from the Petri net (1)\n"
        smt_input += self.ptnet.smtlib_declare_places(1)

        smt_input += "; Assert reduction equations\n"
        smt_input += self.system.smtlib(1, 1)

        smt_input += "; Transition relation: 0 -> 1\n"
        smt_input += self.ptnet_reduced.smtlib_transition_relation(0, eq=False)

        smt_input += "; Formula to check the satisfiability (1)\n"
        smt_input += self.formula.R.smtlib(1, assertion=True)

        smt_input += "; Check satisfiability\n"
        smt_input += "(check-sat)\n"

        return smt_input

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[INDUCTION] RUNNING")
        self.solver =  Z3(debug=self.debug, solver_pids=self.solver_pids)

        if self.ptnet_reduced is None:
            induction = self.prove_without_reduction()
        else:
            induction = self.prove_with_reduction()

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted or induction is None
        if self.solver.aborted or induction is None:
            return

        if induction:
            verdict = Verdict.CEX
        else:
            verdict = Verdict.INV
            if self.path_proof or self.check_proof:
                self.manage_certificate()

        # Put the result in the queue
        result.put((verdict, None))

        # Terminate concurrent methods
        send_signal_pids(concurrent_pids.get(), STOP)

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri Net.
        """
        info("[INDUCTION] > Declaration of the places from the Petri net (0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        info("[INDUCTION] > Push")
        self.solver.push()

        info("[INDUCTION] > Initial marking of the Petri net")
        self.solver.write(self.ptnet.smtlib_initial_marking(0))

        info("[INDUCTION] > Assert feared states (0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        if self.solver.check_sat():
            return True

        info("[INDUCTION] > Pop")
        self.solver.pop()

        info("[INDUCTION] > Assert safe states (0)")
        self.solver.write(self.formula.P.smtlib(0, assertion=True))

        info("[INDUCTION] > Declaration of the places from the Petri net (iteration: 1)")
        self.solver.write(self.ptnet.smtlib_declare_places(1))

        info("[INDUCTION] > Transition relation: 0 -> 1")
        self.solver.write(self.ptnet.smtlib_transition_relation(0, eq=False))

        info("[INDUCTION] > Formula to check the satisfiability (iteration: 1)")
        self.solver.write(self.formula.R.smtlib(1, assertion=True))

        if not self.solver.check_sat():
            return False

        return None

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        info("[INDUCTION] > Declaration of the places from the Petri net (0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        info("[K-INDUCTION] > Assert reduction equations")
        self.solver.write(self.system.smtlib(0, 0))

        info("[INDUCTION] > Push")
        self.solver.push()

        info("[INDUCTION] > Initial marking of the reduced Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_initial_marking(0))

        info("[INDUCTION] > Assert feared states (0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        if self.solver.check_sat():
            return True

        info("[INDUCTION] > Pop")
        self.solver.pop()

        info("[INDUCTION] > Assert safe states (0)")
        self.solver.write(self.formula.P.smtlib(0, assertion=True))

        info("[INDUCTION] > Declaration of the places from the Petri net (1)")
        self.solver.write(self.ptnet.smtlib_declare_places(1))

        info("[K-INDUCTION] > Assert reduction equations")
        self.solver.write(self.system.smtlib(1, 1))

        info("[INDUCTION] > Transition relation: 0 -> 1")
        self.solver.write(
            self.ptnet_reduced.smtlib_transition_relation(0, eq=False))

        info("[INDUCTION] > Formula to check the satisfiability (iteration: 1)")
        self.solver.write(self.formula.R.smtlib(1, assertion=True))

        if not self.solver.check_sat():
            return False

        return None

    def manage_certificate(self) -> None:
        """ Invariance certificate management.
        """
        certificate(self.ptnet, self.formula, self.formula.P.smtlib(), path=self.path_proof, check=self.check_proof)
