"""
Parallelizer for portfolio method

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
__version__ = "4.0.0"

import time
from multiprocessing import Process, Queue
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.checkers.bmc import BMC
from smpt.checkers.cp import CP
from smpt.checkers.enumerative import Enumerative
from smpt.checkers.induction import Induction
from smpt.checkers.kinduction import KInduction
from smpt.checkers.pdr import PDR
from smpt.checkers.randomwalk import RandomWalk
from smpt.checkers.statequation import StateEquation
from smpt.exec.utils import KILL, send_signal_group_pid, send_signal_pids
from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import Marking, PetriNet
from smpt.ptio.system import System
from smpt.ptio.verdict import Verdict

PRE_TIMEOUT = 120


class Parallelizer:
    """ Helper to manage methods in parallel.

    Attributes
    ----------
    property_id : str
        Id of the property.
    formula : Formula
        Reachability formula.
    show_techniques : bool
        Show techniques flag.
    show_time : bool
        Show time flag.
    show_model : bool
        Show model flag.
    additional_techniques : Queue of str
        Queue of additional techniques involved during the computation ('TOPOLOGICAL', 'NUPN_NUPN', ...).
    methods : list of AbstractChecker
        List of methods to be run in parallel.
    processes : list of Process
        List of processes corresponding to the methods.
    techniques : list of list of str
        List of techniques corresponding to the methods.
    computation_time : float
        Computation time.
    results : list of Queue of tuple of Verdict, Marking
        List of Queue to store the verdicts corresponding to the methods.
    solver_pids : Queue of int
        Queue of solver pids.
    """

    def __init__(self, property_id: str, ptnet: PetriNet, formula: Formula, methods: list[str], ptnet_reduced: Optional[PetriNet] = None, system: Optional[System] = None, show_techniques: bool = False, show_time: bool = False, show_model: bool = False, debug: bool = False, path_markings: Optional[str] = None, check_proof: bool = False, path_proof: Optional[str] = None, mcc: bool = False):
        """ Initializer.

        Parameters
        ----------
        property_id : str
            Id of the property.
        ptnet : PetriNet
            Initial Petri net.
        formula : Formula
            Reachability formula.
        methods : list of str
            List of methods to be run in parallel.
        ptnet_reduced : PetriNet, optional
            Reduced Petri net.
        system : System, optional
            System of reduction equations.
        show_techniques : bool, optional 
            Show techniques flag.
        show_time : bool, optional
            Show time flag.
        show_model : bool, optional
            Show model flag.
        debug : bool, optional
            Debugging flag.
        path_markings : str, optional
            Path to the list of markings (.aut format).
        check_proof : bool, optional
            Check proof flag.
        path_proof : str, optional
            Path to proof.
        mcc : bool, optional
            MCC mode.
        """
        # Property id and corresponding formula
        self.property_id: str = property_id
        self.formula: Formula = formula

        # Output flags
        self.show_techniques: bool = show_techniques
        self.show_time: bool = show_time
        self.show_model: bool = show_model

        # Common techniques
        collateral_processing, unfolding_to_pt, structural_reduction = [], [], []
        if len(methods) > 1:
            collateral_processing = ['COLLATERAL_PROCESSING']
        if ptnet.colored:
            unfolding_to_pt = ['UNFOLDING_TO_PT']
        if ptnet_reduced is not None:
            structural_reduction = ['STRUCTURAL_REDUCTION']
        self.additional_techniques: Queue[str] = Queue()

        # Process information
        self.methods: list[AbstractChecker] = []
        self.processes: list[Process] = []
        self.techniques: list[list[str]] = []
        self.computation_time: float = 0

        # Create queues to store the results
        self.results: list[Queue[tuple[Verdict, Marking]]] = [Queue()
                                                              for _ in methods]

        # Create queue to store solver pids
        self.solver_pids: Queue[int] = Queue()

        # If K-Induction enabled create a queue to store the current iteration of BMC
        induction_queue: Optional[Queue[int]] = None
        if 'K-INDUCTION' in methods:
            induction_queue = Queue()

        # Initialize methods
        for method in methods:

            if method == 'WALK':
                self.methods.append(RandomWalk(
                    ptnet, formula, debug=debug, solver_pids=self.solver_pids))
                self.techniques.append(
                    collateral_processing + unfolding_to_pt + ['WALK'])

            if method == 'STATE-EQUATION':
                self.methods.append(StateEquation(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, mcc=mcc,
                                    debug=debug, solver_pids=self.solver_pids, additional_techniques=self.additional_techniques))
                self.techniques.append(collateral_processing + unfolding_to_pt +
                                       structural_reduction + ['IMPLICIT', 'SAT-SMT', 'STATE_EQUATION'])

            if method == 'INDUCTION':
                self.methods.append(Induction(ptnet, formula, ptnet_reduced=ptnet_reduced,
                                    system=system, show_model=show_model, debug=debug, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt +
                                       structural_reduction + ['IMPLICIT', 'SAT-SMT', 'INDUCTION'])

            if method == 'BMC':
                self.methods.append(BMC(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, show_model=show_model, debug=debug, path_proof=path_proof,
                                    induction_queue=induction_queue, solver_pids=self.solver_pids, additional_techniques=self.additional_techniques))
                self.techniques.append(collateral_processing + unfolding_to_pt +
                                       structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING'])

            if method == 'K-INDUCTION':
                self.methods.append(KInduction(
                    ptnet, formula, debug=debug, induction_queue=induction_queue, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt +
                                       structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING'])

            if method == 'PDR-COV':
                self.methods.append(PDR(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system,
                                    debug=debug, check_proof=check_proof, path_proof=path_proof, method='COV', solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt +
                                       structural_reduction + ['IMPLICIT', 'SAT-SMT', 'PDR-COV'])

            if method == 'PDR-REACH':
                self.methods.append(PDR(ptnet, formula, debug=debug, check_proof=check_proof,
                                    path_proof=path_proof, method='REACH', saturation=False, solver_pids=self.solver_pids))
                self.techniques.append(
                    collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT', 'PDR-REACH'])

            if method == 'PDR-REACH-SATURATED':
                self.methods.append(PDR(ptnet, formula, debug=debug, check_proof=check_proof,
                                    path_proof=path_proof, method='REACH', saturation=True, solver_pids=self.solver_pids))
                self.techniques.append(
                    collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT', 'PDR-REACH-SATURATED'])

            if method == 'SMT':
                self.methods.append(CP(ptnet, formula, system, show_model=show_model,
                                    debug=debug, minizinc=False, solver_pids=self.solver_pids))
                self.techniques.append(
                    collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT'])

            if method == 'CP':
                self.methods.append(CP(ptnet, formula, system, show_model=show_model,
                                    debug=debug, minizinc=True, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt +
                                       structural_reduction + ['IMPLICIT', 'CONSTRAINT_PROGRAMMING'])

            if method == 'ENUM':
                self.methods.append(Enumerative(
                    path_markings, ptnet, formula, ptnet_reduced, system, debug, solver_pids=self.solver_pids))
                self.techniques.append(
                    collateral_processing + unfolding_to_pt + structural_reduction + ['EXPLICIT', 'SAT-SMT'])

    def run(self, timeout=225) -> Optional[str]:
        """ Run analysis in parrallel.

        Parameters
        ----------
        timeout : int, optional
            Time limit.

        Returns
        -------
        str, optional
            Property id if the computation is completed, None otherwise.
        """
        # Exit if no methods to run
        if not self.methods:
            return None

        # Create a queue to share the pids of the concurrent methods
        concurrent_pids: Queue[list[int]] = Queue()

        # Create processes
        self.processes = [Process(target=method.prove, args=(
            result, concurrent_pids,)) for method, result in zip(self.methods, self.results)]

        # Start processes
        pids = []
        for proc in self.processes:
            proc.start()
            pids.append(proc.pid)
        concurrent_pids.put(pids)

        return self.handle(timeout)

    def handle(self, timeout: int) -> Optional[str]:
        """ Handle the methods.

        Parameters
        ----------
        timeout : int
            Time limit.

        Returns
        -------
        str, optional
            Property id if the computation is completed, None if the time limit is reached.
        """
        # Get the starting time
        start_time = time.time()

        # Join processes
        # Wait for the first process
        self.processes[0].join(timeout=timeout)
        # Wait for the other processes (in case of aborted method)
        if len(self.processes) > 1:
            for proc in self.processes[1:]:
                proc.join(timeout=timeout - (time.time() - start_time))

        # Get the computation time
        self.computation_time += time.time() - start_time

        # Return result data if one method finished
        for result_method, techniques in zip(self.results, self.techniques):
            if not result_method.empty():

                verdict, model = result_method.get()
                output = "\nFORMULA {} {}".format(
                    self.property_id, self.formula.result(verdict))

                # Show techniques
                if self.show_techniques:
                    if self.additional_techniques is not None:
                        while not self.additional_techniques.empty():
                            techniques.append(self.additional_techniques.get())
                    output += " TECHNIQUES {}".format(' '.join(techniques))

                # Show computation time
                if self.show_time:
                    output += " TIME {}".format(self.computation_time)

                print(output)

                # Show model
                if self.show_model and model is not None:
                    print("# Model:{}".format(model))

                self.stop()
                return self.property_id

        # Otherwise stop the methods
        self.stop()

        return None

    def stop(self) -> None:
        """ Stop the methods.
        """
        # Kill methods
        send_signal_pids([proc.pid for proc in self.processes], KILL)
        del self.methods

        # Kill solvers
        while not self.solver_pids.empty():
            send_signal_group_pid(self.solver_pids.get(), KILL)


def worker(parallelizer: Parallelizer) -> Optional[str]:
    """ Call run method n parallelizer object.

    Parameters
    ----------
    parallelizer : Parallelizer
        Parallelizer object to run.

    Returns
    -------
    str, optional
        Property id if the computation is completed, None otherwise.
    """
    return parallelizer.run(PRE_TIMEOUT)
