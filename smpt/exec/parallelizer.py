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

from multiprocessing import Process, Queue
from time import time
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
RATIO_LIMIT = 0.8


class Parallelizer:
    """ Helper to manage methods in parallel.

    Attributes
    ----------
    ptnet : PetriNet
        Initial Petri net.
    ptnet_reduced : PetriNet, optional
        Reduced Petri net.
    system : System, optional
        System of reduction equations.
    property_id : str
        Id of the property.
    formula : Formula
        Reachability formula.
    ptnet_skeleton : PetriNet, optional
        Skeleton of a colored Petri net.
    formula_skeleton : Formula, optional
        Formula for skeleton.
    methods : list of str
        List of methods to be run in parallel.
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
    parikh_timeout : int, optional
        Timeout for Parikh walking (if not None).
    check_proof : bool, optional
        Check proof flag.
    path_proof : str, optional
        Path to proof.
    pre_run : bool, optional
        Pre-run mode (mainly for STATE-EQUATION).
    additional_techniques : Queue of str
        Queue of additional techniques involved during the computation ('TOPOLOGICAL', 'USE_NUPN', ...).
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
    induction_queue : Queue of int, optional
        Queue for the exchange with K-INDUCTION.
    ptnet_walk : PetriNet
        Net used for walking.
    formula_walk : Formula
        Formula used for walking.
    projection : bool
        Shadow-completeness of an eventual projection.
    ptnet_switched : PetriNet
        Net used for BMC / K-INDUCTION.
    formula_switched : Formula
        Formulas used for BMC / K-INDUCTION.
    """
    def __init__(self, property_id: str, ptnet: PetriNet, formula: Formula, methods: list[str], ptnet_reduced: Optional[PetriNet] = None, system: Optional[System] = None, ptnet_tfg: Optional[PetriNet] = None, projected_formula: Optional[Formula] = None, ptnet_skeleton: Optional[PetriNet] = None, formula_skeleton: Optional[Formula] = None, show_techniques: bool = False, show_time: bool = False, show_model: bool = False, debug: bool = False, path_markings: Optional[str] = None, parikh_timeout: Optional[int] = None, check_proof: bool = False, path_proof: Optional[str] = None, mcc: bool = False,  pre_run: bool = False):
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
        ptnet_tfg : PetriNet, optional
            Reduced Petri net (TFG).
        projected_formula : Formula, optional
            Projected formula.
        ptnet_skeleton : PetriNet, optional
            Skeleton of a colored Petri net.
        formula_skeleton : Formula, optional
            Formula for skeleton.
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
        parikh_timeout : int, optional
            Timeout for Parikh walking (if not None).
        check_proof : bool, optional
            Check proof flag.
        path_proof : str, optional
            Path to proof.
        mcc : bool, optional
            MCC mode.
        pre_run : bool, optional
            Pre-run mode (mainly for STATE-EQUATION).
        """
        # Petri nets
        self.ptnet: PetriNet = ptnet
        self.ptnet_reduced: Optional[PetriNet] = ptnet_reduced
        self.system: Optional[System] = system

        # Property id and corresponding formula
        self.property_id: str = property_id
        self.formula: Formula = formula

        # Skeleton and corresponding formula
        self.ptnet_skeleton: Optional[PetriNet] = ptnet_skeleton
        self.formula_skeleton: Optional[Formula] = formula_skeleton

        # Methods
        self.methods: list[str] = methods

        # Output flags
        self.show_techniques: bool = show_techniques
        self.show_time: bool = show_time
        self.show_model: bool = show_model
        self.debug: bool = debug

        # Path to markings
        self.path_markings: Optional[str] = path_markings

        # Parikh timeout
        self.parikh_timeout: Optional[int] = parikh_timeout

        # Proof
        self.check_proof: bool = check_proof
        self.path_proof: str = path_proof

        # Pre-run mode
        self.pre_run: bool = pre_run

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
        self.processes: list[Process] = []
        self.techniques: list[list[str]] = []
        self.computation_time: float = 0

        # Create queues to store the results
        self.results: list[Queue[tuple[Verdict, Marking]]] = [Queue()
                                                              for _ in methods]

        # Create queue to store solver pids
        self.solver_pids: Queue[int] = Queue()

        # If K-Induction enabled create a queue to store the current iteration of BMC
        self.induction_queue: Optional[Queue[int]] = None
        if 'K-INDUCTION' in methods:
            self.induction_queue = Queue()

        # Petri net / Formula selection
        #
        # WALK
        # (ptnet_tfg + projected formula if possible, but in mcc mode keep only complete projections)
        self.ptnet_walk: PetriNet = ptnet_tfg if ptnet_tfg is not None and projected_formula is not None and (not mcc or projected_formula.shadow_complete) else ptnet
        self.formula_walk: Formula = projected_formula if ptnet_tfg is not None and projected_formula is not None and (not mcc or projected_formula.shadow_complete) else formula
        #
        # BMC / K-INDUCTION / PDR-COV
        # (ptnet_tfg + projected formula if possible, and in mcc mode only if the ratio > RATIO_LIMIT)
        # print(len(ptnet_reduced.transitions) / len(ptnet_tfg.transitions))
        bad_ratio = ptnet_reduced and ptnet_tfg and ptnet_tfg.transitions and len(ptnet_reduced.transitions) / len(ptnet_tfg.transitions) <= RATIO_LIMIT
        projection: bool = projected_formula is not None and projected_formula.shadow_complete and not (mcc and bad_ratio)
        # Petri net and formula
        self.ptnet_switched: PetriNet = ptnet_tfg if projection else ptnet
        self.formula_switched: Formula = projected_formula if projection else formula
        # Optional reductions
        self.optional_ptnet_reduced: Optional[PetriNet] = None if projection else ptnet_reduced
        self.optional_system: Optional[System] = None if projection else system

        # Initialize methods
        for method in methods:

            if method == 'WALK':
                self.techniques.append(collateral_processing + unfolding_to_pt + ['WALK'])

            if method == 'STATE-EQUATION':
                self.techniques.append(collateral_processing + ['IMPLICIT', 'SAT-SMT', 'STATE_EQUATION'])

            if method == 'INDUCTION':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'INDUCTION'])

            if method == 'BMC':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING'])

            if method == 'K-INDUCTION':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING'])

            if method == 'PDR-COV':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'PDR-COV'])

            if method == 'PDR-REACH':
                self.techniques.append(collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT', 'PDR-REACH'])

            if method == 'PDR-REACH-SATURATED':
                self.techniques.append(collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT', 'PDR-REACH-SATURATED'])

            if method == 'SMT':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT'])

            if method == 'CP':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'CONSTRAINT_PROGRAMMING'])

            if method == 'TIPX':
                self.techniques.append(collateral_processing + unfolding_to_pt + ['TIPX'])

            if method == 'ENUM':
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['EXPLICIT', 'SAT-SMT'])

    def __getstate__(self):
        # Capture what is normally pickled
        state = self.__dict__.copy()

        # Remove unpicklable variable 
        state['processes'] = None
        return state

    def prove(self, method: str, result, concurrent_pids: Queue[list[int]]) -> None:
        """ Prover method instantiator and runner.

        Parameters
        ----------
        method : str
            Method used for proving. 
        concurrent_pids : Queue of list of int
            Queue to share the PIDs of the concurrent methods (to kill if solved).
        """
        prover : Optional[AbstractChecker] = None

        if method == 'WALK':
            prover = RandomWalk(self.ptnet_walk, self.formula_walk, tipx=False, parikh_timeout=self.parikh_timeout, debug=self.debug, solver_pids=self.solver_pids)

        if method == 'STATE-EQUATION':
            prover = StateEquation(self.ptnet, self.formula, ptnet_reduced=self.optional_ptnet_reduced, system=self.optional_system, ptnet_skeleton=self.ptnet_skeleton, formula_skeleton=self.formula_skeleton, pre_run=self.pre_run, debug=self.debug, solver_pids=self.solver_pids, additional_techniques=self.additional_techniques)

        if method == 'INDUCTION':
            prover = Induction(self.ptnet, self.formula, ptnet_reduced=self.ptnet_reduced, system=self.system, show_model=self.show_model, debug=self.debug, solver_pids=self.solver_pids)

        if method == 'BMC':
            prover = BMC(self.ptnet_switched, self.formula_switched, ptnet_reduced=self.optional_ptnet_reduced, system=self.optional_system, show_model=self.show_model, debug=self.debug, check_proof=self.check_proof, path_proof=self.path_proof, induction_queue=self.induction_queue, solver_pids=self.solver_pids, additional_techniques=self.additional_techniques)

        if method == 'K-INDUCTION':
            prover = KInduction(self.ptnet_switched, self.formula_switched, debug=self.debug, induction_queue=self.induction_queue, solver_pids=self.solver_pids)

        if method == 'PDR-COV':
            prover = PDR(self.ptnet_switched, self.formula_switched, ptnet_reduced=self.optional_ptnet_reduced, system=self.optional_system, debug=self.debug, check_proof=self.check_proof, path_proof=self.path_proof, method='COV', solver_pids=self.solver_pids)

        if method == 'PDR-REACH':
            prover = PDR(self.ptnet_switched, self.formula_switched, debug=self.debug, check_proof=self.check_proof, path_proof=self.path_proof, method='REACH', saturation=False, solver_pids=self.solver_pids)

        if method == 'PDR-REACH-SATURATED':
            prover = PDR(self.ptnet_switched, self.formula_switched, debug=self.debug, check_proof=self.check_proof, path_proof=self.path_proof, method='REACH', saturation=True, solver_pids=self.solver_pids)

        if method == 'SMT':
            prover = CP(self.ptnet_switched, self.formula_switched, self.system, show_model=self.show_model, debug=self.debug, minizinc=False, solver_pids=self.solver_pids)

        if method == 'CP':
            prover = CP(self.ptnet, self.formula, self.system, show_model=self.show_model, debug=self.debug, minizinc=True, solver_pids=self.solver_pids)

        if method == 'TIPX':
            prover = RandomWalk(self.ptnet_walk, self.formula_walk, tipx=True, debug=self.debug, solver_pids=self.solver_pids)

        if method == 'ENUM':
            prover = Enumerative(self.path_markings, self.ptnet, self.formula, self.ptnet_reduced, self.system, self.debug, solver_pids=self.solver_pids)

        if prover:
            prover.prove(result, concurrent_pids)

    def run(self, timeout=225) -> Optional[str]:
        """ Run analysis in parallel.

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

        # Create and start processes
        pids = []
        for method, result in zip(self.methods, self.results):
            proc = Process(target=self.prove, args=(method, result, concurrent_pids,))
            proc.start()
            pids.append(proc.pid)
            self.processes.append(proc)
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
        start_time = time()

        # Join processes
        # Wait for the first process
        self.processes[0].join(timeout=timeout)
        # Wait for the other processes (in case of aborted method)
        if len(self.processes) > 1:
            for proc in self.processes[1:]:
                proc.join(timeout=timeout - (time() - start_time))

        # Get the computation time
        self.computation_time += time() - start_time

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


def worker(parallelizer: Parallelizer, timeout: int = PRE_TIMEOUT) -> Optional[str]:
    """ Call run method n parallelizer object.

    Parameters
    ----------
    parallelizer : Parallelizer
        Parallelizer object to run.
    timeout : int, optional
        Time limit.

    Returns
    -------
    str, optional
        Property id if the computation is completed, None otherwise.
    """
    return parallelizer.run(timeout)
