"""
k-induction Method

Based on:
Mary Sheeran, Satnam Singh, and Gunnar Stälmarck.
Checking safety properties using induction and a SAT-solver. 
FMCAD 2000

Adapted for Petri nets

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
from smpt.interfaces.z3 import Z3
from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import Marking, PetriNet
from smpt.ptio.system import System
from smpt.ptio.verdict import Verdict


class KInduction(AbstractChecker):
    """ k-induction method.

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
    state_equation : bool
        Use of the state-equation.
    induction_queue : Queue of int, optional
        Queue for the exchange with k-induction.
    solver : Z3
        SMT solver (Z3).
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, ptnet_reduced: Optional[PetriNet] = None, system: Optional[System] = None, state_equation: bool = False, debug: bool = False, induction_queue: Optional[Queue[int]] = None, solver_pids: Optional[Queue[int]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet : PetriNet
            Initial Petri net.
        formula : Formula
            Reachability formula.
        ptnet_reduced : PetriNet, optional
            Reduced Petri net.
        system : System, optional
            System of reduction equations.
        state_equation : bool, optional
            Use of the state-equation.
        debug : bool, optional
            Debugging flag.
        induction_queue : Queue of int, optional
            Queue for the exchange with k-induction.
        solver_pids : Queue of int, optional
            Queue to share the current PID.
        """
        # Initial Petri net
        self.ptnet: PetriNet = ptnet

        # Reduced Petri net
        self.ptnet_reduced: Optional[PetriNet] = ptnet_reduced

        # System of linear equations
        self.system: Optional[System] = system

        # Formula to study
        self.formula: Formula = formula

        # Use of the state-equation
        self.state_equation = state_equation

        # Queue shared with BMC
        self.induction_queue: Optional[Queue[int]] = induction_queue

        # SMT solver (with strong memory limit because BMC is necessary and not k-induction)
        self.solver: Optional[Z3] = None
        self.debug = debug
        self.solver_pids = solver_pids

    def smtlib(self, k: int) -> str:
        """ Output for understanding.

        Parameters
        ----------
        k : int
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction(k)
        else:
            smt_input = self.smtlib_with_reduction(k)

        smt_input += "(check-sat)\n"

        return smt_input

    def smtlib_without_reduction(self, k: int) -> str:
        """ Helper for understanding (without reduction).

        Parameters
        ----------
        k : int
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net (iteration: 0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        for i in range(k):
            smt_input += "; Assert states safes (iteration:{})\n".format(i)
            smt_input += self.formula.P.smtlib(i, assertion=True)

            smt_input += "; Declaration of the places from the Petri net (iteration: {})\n".format(1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet.smtlib_transition_relation(i, eq=False)

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(k, assertion=True)

        return smt_input

    def smtlib_with_reduction(self, k: int) -> str:
        """ Helper for understanding (with reduction).

        Parameters
        ----------
        k : int
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the initial net (iteration: 0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Assert reduction equations\n"
        smt_input += self.system.smtlib(0, 0)

        for i in range(k):

            smt_input += "; Assert safe states (iteration: {})\n".format(i)
            smt_input += self.formula.P.smtlib(i, assertion=True)

            smt_input += "; Declaration of the places from the initial net (iteration: {})\n".format(i + 1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1)

            smt_input += "; Assert reduction equations\n"
            smt_input += self.system.smtlib(i + 1, i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet_reduced.smtlib_transition_relation(i, eq=False)

        smt_input += "; Formula to check the satisfiability (iteration: {})\n".format(k)
        smt_input += self.formula.R.smtlib(k, assertion=True)

        return smt_input

    def prove(self, result: Queue[tuple[Verdict, Marking]], concurrent_pids: Queue[list[int]]) -> None:
        """ Prover.

        Parameters
        ----------
        result : Queue of tuple of Verdict, Marking
            Not used.
        concurrent_pids : Queue of int
            Not used.
        """
        info("[K-INDUCTION] RUNNING")
        self.solver = Z3(strong_memory_limit=True, debug=self.debug, solver_pids=self.solver_pids)

        if self.ptnet_reduced is None:
            iteration = self.prove_without_reduction()
        else:
            iteration = self.prove_with_reduction()

        if not self.solver.aborted and self.induction_queue is not None:
            self.induction_queue.put(iteration)

        # Kill the solver
        self.solver.kill()

    def prove_without_reduction(self) -> int:
        """ Prover for non-reduced Petri Net.

        Returns
        -------
        int
            Order of the counter-example.
        """
        info("[K-INDUCTION] > Initialization")

        info("[K-INDUCTION] > Declaration of the places from the Petri net (iteration: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        k = 0
        info("[K-INDUCTION] > k = 0")

        info("[K-INDUCTION] > Push")
        self.solver.push()

        info("[K-INDUCTION] > Formula to check the satisfiability (iteration: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        while self.solver.check_sat() and not self.solver.aborted:

            info("[K-INDUCTION] > Pop")
            self.solver.pop()

            info("[K-INDUCTION] > Assert states safe (iteration: {})".format(k))
            self.solver.write(self.formula.P.smtlib(k, assertion=True))

            if self.state_equation and not k:
                info("[K-INDUCTION] > Declaration of the transitions from the Petri net")
                self.solver.write(self.ptnet.smtlib_declare_transitions())
                info("[K-INDUCTION] > State Equation")
                self.solver.write(self.ptnet.smtlib_state_equation(0))
                info("[K-INDUCTION] > Add read arc constraints")
                self.solver.write(self.ptnet.smtlib_read_arc_constraints())

            k += 1
            info("[K-INDUCTION] > k = {}".format(k))

            info("[K-INDUCTION] > Declaration of the places from the Petri net (iteration: {})".format(k))
            self.solver.write(self.ptnet.smtlib_declare_places(k))

            info("[K-INDUCTION] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(
                self.ptnet.smtlib_transition_relation(k - 1, eq=False))

            info("[K-INDUCTION] > Push")
            self.solver.push()

            info("[K-INDUCTION] > Formula to check the satisfiability (iteration: {})".format(k))
            self.solver.write(self.formula.R.smtlib(k, assertion=True))

        return k

    def prove_with_reduction(self) -> int:
        """ Prover for reduced Petri Net.

        Returns
        -------
        int
            Order of the counter-example.

        Note
        ----
        Reduction can deteriorate the performances.
        Sometimes the existential variable avoids termination. 
        """
        info("[K-INDUCTION] > Initialization")

        info("[K-INDUCTION] > Declaration of the places from the initial net (iteration: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        info("[K-INDUCTION] > Assert reduction equations")
        self.solver.write(self.system.smtlib(0, 0))

        info("[K-INDUCTION] > Push")
        self.solver.push()

        k = 0
        info("[K-INDUCTION] > k = 0")

        info("[K-INDUCTION] > Formula to check the satisfiability (iteration: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        while self.solver.check_sat() and not self.solver.aborted:

            info("[K-INDUCTION] > Pop")
            self.solver.pop()

            info("[K-INDUCTION] > Assert safe states (iteration: {})".format(k))
            self.solver.write(self.formula.P.smtlib(k, assertion=True))

            if self.state_equation and not k:
                info("[K-INDUCTION] > Declaration of the transitions from the Petri net")
                self.solver.write(self.ptnet_reduced.smtlib_declare_transitions())
                info("[K-INDUCTION] > State Equation")
                self.solver.write(self.ptnet_reduced.smtlib_state_equation(0))
                info("[K-INDUCTION] > Add read arc constraints")
                self.solver.write(self.ptnet_reduced.smtlib_read_arc_constraints())

            k += 1
            info("[K-INDUCTION] > k = {}".format(k))

            info("[K-INDUCTION] > Declaration of the places from the initial net (iteration: {})".format(k))
            self.solver.write(self.ptnet.smtlib_declare_places(k))

            info("[K-INDUCTION] > Assert reduction equations")
            self.solver.write(self.system.smtlib(k, k))

            info("[K-INDUCTION] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(
                self.ptnet_reduced.smtlib_transition_relation(k - 1, eq=False))

            info("[K-INDUCTION] > Push")
            self.solver.push()

            info("[K-INDUCTION] > Formula to check the satisfiability (iteration: {})".format(k))
            self.solver.write(self.formula.R.smtlib(k, assertion=True))

        return k
