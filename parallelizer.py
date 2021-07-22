"""
Parallelizer for BMC and IC3 Analysis Methods

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
__version__ = "3.0.0"

import sys
import time
from multiprocessing import Process, Queue

from bmc import BMC
from cp import CP
from enumerative import Enumerative
from ic3 import IC3
from pdr import PDR
from properties import Formula
from ptnet import PetriNet
from system import System
from utils import RESUME, STOP, SUSPEND, send_signal


class Parallelizer:
    """ Analysis methods parallelizer.
    """

    def __init__(self, property_id, ptnet, formula, ptnet_reduced=None, system=None, show_techniques=False, show_time=False, show_model=False, debug=False, methods=[], path_markings=None):
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
        self.methods, self.process, self.techniques  = [], [], []
        self.computation_time = 0

        # Create queues to store the results
        self.results = [Queue() for _ in methods]

        # Initialize methods
        for method in methods:
            if method == 'BMC':
                self.methods.append(BMC(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, show_model=show_model, debug=debug))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT', 'NET_UNFOLDING'])

            if method == 'PDR-COV':
                self.methods.append(IC3(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug, method='COV'))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT'])

            if method == 'PDR-REACH':
                self.methods.append(IC3(ptnet, formula, debug=debug, method='REACH'))
                self.techniques.append(collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT'])

            if method == 'PDR-H':
                self.methods.append(PDR(ptnet, formula, debug=debug))
                self.techniques.append(collateral_processing + unfolding_to_pt + ['IMPLICIT', 'SAT-SMT'])

            if method == 'SMT':
                self.methods.append(CP(ptnet, formula, system, show_model=show_model, debug=debug, minizinc=False))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'SAT-SMT'])

            if method == 'CP':
                self.methods.append(CP(ptnet, formula, system, show_model=show_model, debug=debug, minizinc=True))
                self.techniques.append(collateral_processing + unfolding_to_pt + structural_reduction + ['IMPLICIT', 'CONSTRAINT_PROGRAMMING'])

            if method == 'ENUM':
                self.methods.append(Enumerative(path_markings, ptnet, formula, ptnet_reduced, system, debug))
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

        # Create daemon process
        self.process = [Process(target=method.prove, args=(result,concurrent_pids,)) for method, result in zip(self.methods, self.results)]

        # Start process
        pids = []
        for proc in self.process:
            proc.start()
            pids.append(proc.pid)
        concurrent_pids.put(pids)

        return self.handle(timeout)

    def resume(self, timeout):
        """ Resume the methods.
        """
        # Resume methods
        for method in self.methods:
            method.solver.resume()

        # Resume process
        send_signal([proc.pid for proc in self.process], RESUME)
        return self.handle(timeout)

    def handle(self, timeout):
        """ Handle the methods.
        """
        # Get the starting time
        start_time = time.time()

        # Join process
        # Wait for the first process
        self.process[0].join(timeout=timeout)
        # Wait for the other process (in case of aborted method)
        if len(self.process) > 1:
            for proc in self.process[1:]:
                proc.join(timeout=timeout - (time.time() - start_time))
        
        # Get the computation time
        self.computation_time += time.time() - start_time

        # Return result data if one method finished
        for result_method, techniques in zip(self.results, self.techniques):
            if not result_method.empty():

                sat, model = result_method.get()
                print('FORMULA', self.property_id, self.formula.result(sat), end=' ')
                
                # Show techniques
                if self.show_techniques:
                    print('TECHNIQUES', ' '.join(techniques), end=' ')

                # Show computation time
                if self.show_time:
                    print('TIME', self.computation_time, end=' ')

                print()

                # Show model
                if self.show_model and model is not None:
                    model.show_model()
                
                self.stop()
                return True

        # TODO v4: suspend
        # Otherwise stop the methods
        self.stop()

        return False

    def suspend(self):
        """ Suspend the methods.
        """
        for method in self.methods:
            method.solver.suspend()
        send_signal([proc.pid for proc in self.process], SUSPEND)

    def stop(self):
        """ Stop the methods.
        """
        for method in self.methods:
            method.solver.kill()
        send_signal([proc.pid for proc in self.process], RESUME)
        send_signal([proc.pid for proc in self.process], STOP)

