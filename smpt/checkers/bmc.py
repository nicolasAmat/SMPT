"""
BMC (Bounded Model Checking) Method

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
from os import remove
from tempfile import NamedTemporaryFile
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.play import play
from smpt.interfaces.walk import Walk
from smpt.interfaces.z3 import Z3
from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import Marking, PetriNet
from smpt.ptio.system import System
from smpt.ptio.verdict import Verdict


class BMC(AbstractChecker):
    """ Bounded Model Checking (BMC) method.

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
    debug : bool
        Debugging flag.
    mcc : bool
        MCC mode.
    check_proof : bool
        Check proof flag.
    path_proof : str, optional
        Path to proof (.scn format).
    induction_queue : Queue of int, optional
        Queue for the exchange with k-induction.
    show_model : bool
        Show model flag.
    additional_techniques : Queue of str, optional
        Queue to add some additional technique.
    solver : Z3
        SMT solver (Z3).
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, ptnet_reduced: Optional[PetriNet] = None, system: Optional[System] = None, show_model: bool = False, debug: bool = False, mcc: bool = False, check_proof: bool = False, path_proof: Optional[str] = None, induction_queue: Optional[Queue[int]] = None, solver_pids: Optional[Queue[int]] = None, additional_techniques: Optional[Queue[str]] = None) -> None:
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
        show_model : bool, optional
            Show model flag.
        debug : bool, optional
            Debugging flag.
        mcc : bool, optional
            MCC mode.
        proof_enabled : bool
            Proof flag.
        check_proof : bool, optional
            Check proof flag.
        path_proof : str, optional
            Path to proof (.scn format).
        induction_queue : Queue of int, optional
            Queue for the exchange with k-induction.
        solver_pids : Queue of int, optional
            Queue to share the current PID.
        additional_techniques : Queue of str, optional
            Queue to add some additional technique.
        path_proof : str
            Path to proof (.scn format)
        """
        # Initial Petri net
        self.ptnet: PetriNet = ptnet

        # Reduced Petri net
        self.ptnet_reduced: Optional[PetriNet] = ptnet_reduced

        # System of linear equations
        self.system: Optional[System] = system

        # Formula to study
        self.formula: Formula = formula

        # Debugging flag
        self.debug: bool = debug

        # MCC mode
        self.mcc: bool = mcc

        # Proof checking options
        self.proof_enabled: bool = check_proof or path_proof is not None
        self.check_proof: bool = check_proof
        self.path_proof: Optional[str] = path_proof

        # Queue shared with K-Induction
        self.induction_queue: Optional[Queue[int]] = induction_queue

        # Show model option
        self.show_model: bool = show_model

        # Additional techniques queue
        self.additional_techniques: Optional[Queue[str]] = additional_techniques

        # SMT solver
        self.solver: Z3 = Z3(debug=debug, solver_pids=solver_pids)

        # Solver pids
        self.solver_pids: Optional[Queue[int]] = solver_pids

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

        smt_input += "; Check satisfiability\n"
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

        smt_input += "; Declaration of the places from the Petri net (order: 0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0, non_negative=False)

        smt_input += "; Initial marking of the Petri net\n"
        smt_input += self.ptnet.smtlib_initial_marking(0)

        for i in range(k):
            smt_input += "; Declaration of the places from the Petri net (order: {})\n".format(i + 1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1, non_negative=False)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet.smtlib_transition_relation(i, eq=False, tr=self.proof_enabled)

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(k + 1, assertion=True)

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

        smt_input += "; Declaration of the places from the initial Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the additional variables\n"
        smt_input += self.system.smtlib_declare_additional_variables()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        smt_input += "; Reduction equations (not involving places from the reduced Petri net)"
        smt_input += self.system.smtlib_equations_without_places_from_reduced_net()

        smt_input += "; Declaration of the places from the reduced Petri net (order: 0)\n"
        smt_input += self.ptnet_reduced.smtlib_declare_places(0, non_negative=False)

        smt_input += "; Initial marking of the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_initial_marking(0)

        for i in range(k):
            smt_input += "; Declaration of the places from the reduced Petri net (order: {})\n".format(1)
            smt_input += self.ptnet_reduced.smtlib_declare_places(i + 1, non_negative=False)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet_reduced.smtlib_transition_relation(i, eq=False, tr=self.proof_enabled)

        smt_input += "; Reduction equations\n"
        smt_input += self.system.smtlib_equations_with_places_from_reduced_net(k)

        smt_input += "; Link initial and reduced Petri nets\n"
        smt_input += self.system.smtlib_link_nets(k)

        return smt_input

    def prove(self, result: Queue[tuple[Verdict, Marking]], concurrent_pids: Queue[list[int]]) -> None:
        """ Prover.

        Parameters
        ----------
        result : Queue of tuple of Verdict, Marking
            Queue to exchange the verdict.
        concurrent_pids : Queue of int
            Queue to get the PIDs of the concurrent methods.
        """
        info("[BMC] RUNNING")

        if self.ptnet_reduced is None:
            order = self.prove_without_reduction()
        else:
            order = self.prove_with_reduction()

        # Quit if the solver has aborted
        if self.solver.aborted:
            if self.mcc:
                walk = Walk(self.ptnet.filename, solver_pids=self.solver_pids)
                if walk.check_sat(self.formula.walk_filename):
                    order = -2
                walk.kill()
            else:
                return

        # Put the result in the queue
        model = None
        if order == -2:
            verdict = Verdict.CEX
            if self.additional_techniques is not None:
                self.additional_techniques.put('WALK')
        elif order == -1:
            verdict = Verdict.INV
            if self.additional_techniques is not None:
                self.additional_techniques.put('K-INDUCTION')
        else:
            verdict = Verdict.CEX
            if self.additional_techniques is not None:
                self.additional_techniques.put('BMC')
            if self.show_model:
                model = self.solver.get_marking(self.ptnet, order)
        result.put((verdict, model))

        # Kill the solver
        self.solver.kill()

        # Terminate concurrent methods
        send_signal_pids(concurrent_pids.get(), STOP)

    def prove_without_reduction(self) -> int:
        """ Prover for non-reduced Petri Net.

        Returns
        -------
        int
            Order of the counter-example.
        """
        info("[BMC] > Initialization")

        info("[BMC] > Declaration of the places from the Petri net (order: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0, non_negative=False))

        info("[BMC] > Initial marking of the Petri net")
        self.solver.write(self.ptnet.smtlib_initial_marking(0))

        info("[BMC] > Push")
        self.solver.push()

        info("[BMC] > Formula to check the satisfiability (order: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        k, k_induction_iteration = 0, float('inf')

        while not self.solver.check_sat() and not self.solver.aborted:

            if self.induction_queue is not None and not self.induction_queue.empty():
                k_induction_iteration = self.induction_queue.get()

            if k >= k_induction_iteration:
                return -1

            info("[BMC] > Pop")
            self.solver.pop()

            k += 1
            info("[BMC] > k = {}".format(k))

            info("[BMC] > Declaration of the places from the Petri net (order: {})".format(k))
            self.solver.write(self.ptnet.smtlib_declare_places(k, non_negative=False))

            info("[BMC] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(self.ptnet.smtlib_transition_relation(k - 1, eq=False, tr=self.proof_enabled))

            info("[BMC] > Push")
            self.solver.push()

            info("[BMC] > Formula to check the satisfiability (order: {})".format(k))
            self.solver.write(self.formula.R.smtlib(k, assertion=True))

        # Proof management
        if self.check_proof or self.path_proof:
            self.proof(self.ptnet, k)

        return k

    def prove_with_reduction(self) -> int:
        """ Prover for reduced Petri Net.

        Returns
        -------
        int
            Order of the counter-example.
        """
        info("[BMC] > Initialization")

        info("[BMC] > Declaration of the places from the initial Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())

        info("[BMC] > Declaration of the additional variables")
        self.solver.write(self.system.smtlib_declare_additional_variables())

        info("[BMC] > Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        info("[BMC] > Reduction equations (not involving places from the reduced Petri net)")
        self.solver.write(self.system.smtlib_equations_without_places_from_reduced_net())

        info("[BMC] > Declaration of the places from the reduced Petri net (order: 0)")
        self.solver.write(self.ptnet_reduced.smtlib_declare_places(0, non_negative=False))

        info("[BMC] > Initial marking of the reduced Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_initial_marking(0))

        info("[BMC] > Push")
        self.solver.push()

        info("[BMC] > Reduction equations")
        self.solver.write(self.system.smtlib_equations_with_places_from_reduced_net(0))

        info("[BMC] > Link initial and reduced Petri nets")
        self.solver.write(self.system.smtlib_link_nets(0))

        if not self.ptnet_reduced.places and not self.solver.check_sat():
            return -1

        k, k_induction_iteration = 0, float('inf')

        while not self.solver.check_sat() and not self.solver.aborted:

            if self.induction_queue is not None and not self.induction_queue.empty():
                k_induction_iteration = self.induction_queue.get()

            if k >= k_induction_iteration:
                return -1

            info("[BMC] > Pop")
            self.solver.pop()

            k += 1
            info("[BMC] > k = {}".format(k))

            info("[BMC] > Declaration of the places from the reduced Petri net (order: {})".format(k))
            self.solver.write(self.ptnet_reduced.smtlib_declare_places(k, non_negative=False))

            info("[BMC] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(self.ptnet_reduced.smtlib_transition_relation(k - 1, eq=False, tr=self.proof_enabled))

            info("[BMC] > Push")
            self.solver.push()

            info("[BMC] > Reduction equations")
            self.solver.write(self.system.smtlib_equations_with_places_from_reduced_net(k))

            info("[BMC] > Link initial and reduced Petri nets")
            self.solver.write(self.system.smtlib_link_nets(k))

        # Proof management
        if self.check_proof or self.path_proof:
            self.proof(self.ptnet_reduced, k)

        return k

    def proof(self, ptnet: PetriNet, trace_length: int) -> None:
        """ Proof management.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.
        trace_length : int
            Trace length.
        """
        trace = ' '.join(self.solver.get_trace(ptnet, trace_length))

        filename = self.path_proof + '.scn' if self.path_proof else NamedTemporaryFile(suffix='.scn', delete=False).name

        with open(filename, 'w') as fp_proof:
            fp_proof.write(trace)

        if self.check_proof:
            print("####################")
            print("[BMC] Trace")
            print(trace)
            print("####################")

            print("[PDR] Trace checking")
            print("Trace fireable form the initial marking:",
                  play(ptnet.filename, filename, self.debug))
            print("####################")

        if not self.path_proof:
            remove(filename)
