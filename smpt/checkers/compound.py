"""
Compound Method

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

from __future__ import annotations

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "5.0"

from logging import info
from multiprocessing import Queue
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.z3 import Z3
from smpt.ptio.formula import Formula, Properties
from smpt.ptio.ptnet import PetriNet
from smpt.ptio.verdict import Verdict


class Compound(AbstractChecker):
    """
    Compound method.
    """

    def __init__(self, formula: Formula, properties: Properties, debug: bool = False, solver_pids: Optional[Queue[int]] = None):
        """ Initializer.
        """
        # Formula
        self.formula = formula

        # Properties context
        self.properties = properties

        # SMT solver
        self.solver = Z3(debug=debug, solver_pids=solver_pids)

    def smtlib(self):
        """ SMT-LIB format for debugging.
        """
        smt_input = self.properties.ptnet.smtlib_declare_places()

        smt_input += '\n'.join(map(lambda P: P.smtlib(assertion=True), self.properties.invariant))
        smt_input += self.formula.R.smtlib(assertion=True)
        
        for property in self.properties.invariant:
            smt_input += property.smtlib(assertion=True)

        for property in self.properties.reachable:
            smt_input += property.smtlib(assertion=True)

        return smt_input

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[COMPOUND] RUNNING")
        self.solver.write(self.properties.ptnet.smtlib_declare_places())

        self.solver.push()
        verdict = self.prove_invariant()

        if verdict == Verdict.UNKNOWN:
            self.solver.pop()
            verdict = self.prove_reachable()
            
        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted or induction is None
        if self.solver.aborted or verdict == Verdict.UNKNOWN:
            return

        # Put the result in the queue
        result.put((verdict, None))

        # Terminate concurrent methods
        send_signal_pids(concurrent_pids.get(), STOP)

    def prove_invariant(self) -> Verdict:
        """ (/\ AG) /\ R UNSAT
        """
        if not self.properties.invariant:
            return Verdict.UNKNOWN

        info("[COMPOUND] Checking (/\ AG) /\ R UNSAT")

        self.solver.write('\n'.join(map(lambda property: property.smtlib(assertion=True), self.properties.invariant)))
        self.solver.write(self.formula.R.smtlib(assertion=True))

        if not self.solver.check_sat():
            return Verdict.INV
        else:
            return Verdict.UNKNOWN

    def prove_reachable(self) -> Verdict:
        """ 
        """
        if not self.properties.invariant and not self.properties.reachable:
            return Verdict.UNKNOWN

        info("[COMPOUND] Checking EF|AG /\ P UNSAT")

        self.solver.write(self.formula.P.smtlib(assertion=True))

        for property in self.properties.invariant:
            self.solver.push()
            self.solver.write(property.smtlib(assertion=True))
            if not self.solver.check_sat():
                return Verdict.CEX
            self.solver.pop()

        for property in self.properties.reachable:
            self.solver.push()
            self.solver.write(property.smtlib(assertion=True))
            if not self.solver.check_sat():
                return Verdict.CEX
            self.solver.pop()

        return Verdict.UNKNOWN
