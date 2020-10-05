#!/usr/bin/env python3

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
__version__ = "2.0.0"

import os
import signal
import sys
import time
from multiprocessing import Process, Queue

import psutil

from bmc import BMC
from ic3 import IC3
from properties import Formula
from ptnet import PetriNet
from system import System


class Parallelizer:
    """ Analysis methods parallelizer.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, display_model=False, debug=False, method_disabled=''):
        """ Initializer.
        """
        self.bmc, self.ic3 = None, None

        # Create a BMC instance if not disabled
        if method_disabled != 'BMC':
            self.bmc = BMC(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, display_model=display_model, debug=debug, parallelizer_pid=os.getpid())

        # Create an IC3 instance if not disabled and if the formula is monotonic
        if method_disabled != 'IC3' and not formula.non_monotonic:
            self.ic3 = IC3(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug, parallelizer_pid=os.getpid())

        self.proc_bmc, self.proc_ic3 = None, None

    def run(self, timeout=60):
        """ Run BMC and IC3 analysis in parrallel.

            Return:
            -`True` if a counterexample is found and `False` otherwise,
            - a counterexample if there is one,
            - execution time.
        """
        # Create queues to store the result
        result_bmc, result_ic3 = Queue(), Queue()

        # Create daemon processes
        if self.bmc:
            self.proc_bmc = Process(target=self.bmc.prove, args=(result_bmc,))
        if self.ic3:
            self.proc_ic3 = Process(target=self.ic3.prove, args=(result_ic3,))

        # Get the starting time
        start_time = time.time()

        # Start processes
        if self.proc_bmc:
            self.proc_bmc.start()
        if self.proc_ic3:
            self.proc_ic3.start()

        # Join the BMC process, if it finishes it will kill the IC3 process
        if self.proc_bmc:
            self.proc_bmc.join(timeout=timeout)

        # Join the IC3 process if BMC is disabled
        if self.proc_ic3 and not self.proc_bmc:
            self.proc_ic3.join(timeout=timeout)

        # Get the execution time
        execution_time = time.time() - start_time

        # Get the BMC result if there is one
        if not result_bmc.empty():
            sat, model = result_bmc.get()
            return sat, model, execution_time, 'BMC'

        # Get the IC3 result if there is one
        if not result_ic3.empty():
            sat = not result_ic3.get()[0]
            return sat, None, execution_time, 'IC3'
        
        # Otherwise exit
        self.stop()
        return None, None, execution_time, ''

    def stop(self):
        """ Stop BMC and IC3 methods.
        """
        # Kill children
        parallelizer_pid = os.getpid()
        parent = psutil.Process(parallelizer_pid)
        children = parent.children(recursive=True)
        for process in children:
            if process.pid != parallelizer_pid:
                try:
                    process.send_signal(signal.SIGTERM)
                except psutil.NoSuchProcess:
                    pass


if __name__ == '__main__':

    if len(sys.argv) < 3:
        sys.exit("Argument missing: ./parallelizer.py <places_to_reach> <path_to_Petri_net> [<path_to_reduced_Petri_net>]")

    ptnet = PetriNet(sys.argv[2])

    marking = {ptnet.places[pl]: 1 for pl in sys.argv[1].split(',')}
    formula = Formula(ptnet)
    formula.generate_reachability(marking)

    if len(sys.argv) == 3:
        ptnet_reduced = None
        system = None
    else:
        ptnet_reduced = PetriNet(sys.argv[3])
        system = System(sys.argv[3], ptnet.places.keys(), ptnet_reduced.places.keys())

    parallelizer = Parallelizer(ptnet, formula, ptnet_reduced, system)

    print("> Result of the parallelized analysis")
    print("-------------------------------------")
    sat, _, _, method = parallelizer.run()
    print("{} {}".format(formula.result(sat), method))
