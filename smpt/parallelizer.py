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

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import time
from multiprocessing import Process, Queue

from bmc import BMC
from cp import CP
from enumerative import Enumerative
from induction import Induction
from kinduction import KInduction
from pdr import PDR
from randomwalk import RandomWalk
from statequation import StateEquation
from utils import KILL, STOP, Verdict, send_signal_group_pid, send_signal_pids


class Parallelizer:
    """ Analysis methods parallelizer.
    """

    def __init__(self, property_id, ptnet, formula, methods, ptnet_reduced=None, system=None, show_techniques=False, show_time=False, show_model=False, debug=False, path_markings=None, check_proof=False, mcc=False):
        """ Initializer.
        """
        # Property id and corresponding formula
        self.property_id = property_id
        self.formula = formula

        # Output flags
        self.show_techniques = show_techniques
        self.show_time = show_time
        self.show_model = show_model

        # Common techniques
        collateral_processing, unfolding_to_pt, structural_reduction = [], [], []
        if len(methods) > 1:
            collateral_processing = ['COLLATERAL_PROCESSING']
        if ptnet.colored:
            unfolding_to_pt = ['UNFOLDING_TO_PT']
        if ptnet_reduced is not None:
            structural_reduction = ['STRUCTURAL_REDUCTION']

        # Process information
        self.methods, self.processes, self.techniques  = [], [], []
        self.computation_time = 0

        # Create queues to store the results
        self.results = [Queue() for _ in methods]

        # Create queue to store solver pids
        self.solver_pids = Queue()

        # If K-Induction enabled create a queue to store the current iteration of BMC
        if 'K-INDUCTION' in methods:
            induction_queue = Queue()
        else:
            induction_queue = None

        # Initialize methods
        for method in methods:

            if method == 'INDUCTION':
                self.methods.append(Induction(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, show_model=show_model, debug=debug, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'INDUCTION'])

            if method == 'BMC':
                self.methods.append(BMC(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, show_model=show_model, debug=debug, induction_queue=induction_queue, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING', 'BMC'])

            if method == 'STATE-EQUATION':
                self.methods.append(StateEquation(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, mcc=mcc, debug=debug, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'STATE_EQUATION'])

            if method == 'WALK':
                self.methods.append(RandomWalk(ptnet, formula, debug=debug, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['WALK'])

            if method == 'K-INDUCTION':
                self.methods.append(KInduction(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, show_model=show_model, debug=debug, induction_queue=induction_queue, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING', 'K-INDUCTION'])

            if method == 'PDR-COV':
                self.methods.append(PDR(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug, check_proof=check_proof, method='COV', solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'PDR-COV'])

            if method == 'PDR-REACH':
                self.methods.append(PDR(ptnet, formula, debug=debug, check_proof=check_proof, method='REACH', saturation=False, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT', 'PDR-REACH'])

            if method == 'PDR-REACH-SATURATED':
                self.methods.append(PDR(ptnet, formula, debug=debug, check_proof=check_proof, method='REACH', saturation=True, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT', 'PDR-REACH-SATURATED'])

            if method == 'SMT':
                self.methods.append(CP(ptnet, formula, system, show_model=show_model, debug=debug, minizinc=False, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT'])

            if method == 'CP':
                self.methods.append(CP(ptnet, formula, system, show_model=show_model, debug=debug, minizinc=True, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'CONSTRAINT_PROGRAMMING'])

            if method == 'ENUM':
                self.methods.append(Enumerative(path_markings, ptnet, formula, ptnet_reduced, system, debug, solver_pids=self.solver_pids))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['EXPLICIT', 'SAT-SMT'])

    def run(self, timeout=225):
        """ Run analysis in parrallel.

            Return `True` if computation is done, `False` otherwise.
        """
        # Exit if no methods to run
        if not self.methods:
            return True

        # Create a queue to share the pids of the concurrent methods
        concurrent_pids = Queue()

        # Create processes
        self.processes = [Process(target=method.prove, args=(result,concurrent_pids,)) for method, result in zip(self.methods, self.results)]

        # Start processes
        pids = []
        for proc in self.processes:
            proc.start()
            pids.append(proc.pid)
        concurrent_pids.put(pids)

        return self.handle(timeout)

    def handle(self, timeout):
        """ Handle the methods.
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
                print('FORMULA', self.property_id, self.formula.result(verdict), end=' ')

                # Show techniques
                if self.show_techniques:
                    if  techniques[-1] == 'BMC' and verdict == Verdict.INV:
                        techniques[-1] = 'K-INDUCTION'
                    print('TECHNIQUES', ' '.join(techniques), end=' ')

                # Show computation time
                if self.show_time:
                    print('TIME', self.computation_time, end=' ')

                print()

                # Show model
                if self.show_model and model is not None:
                    print("# Model:{}".format(model))
                
                self.stop()
                return self.property_id

        # Otherwise stop the methods
        self.stop()

        return None

    def stop(self):
        """ Stop the methods.
        """
        # Kill solvers
        while not self.solver_pids.empty():
            send_signal_group_pid(self.solver_pids.get(), KILL)

        # Kill methods
        send_signal_pids([proc.pid for proc in self.processes], KILL)
        del self.methods

