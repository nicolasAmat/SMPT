#!/usr/bin/env python3

"""
Parallelizer for BMC and IC3 analysis methods.

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

import sys
import time
from threading import Thread

from bmc import BMC, stop_bmc
from ic3 import IC3, stop_ic3
from properties import Formula
from ptnet import PetriNet
from system import System


class Parallelizer:
    """ Analysis methods parallelizer.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False):
        """ Initializer.
        """
        self.bmc = BMC(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug,
                       stop_concurrent=stop_ic3)
        self.ic3 = IC3(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug,
                       stop_concurrent=stop_bmc)

    def run(self, timeout=600):
        """ Run BMC and IC3 analysis in parrallel.

            Return:
            -`True` if a counterexample is found and `False` otherwise,
            - a counterexample if there is one,
            - execution time.
        """
        result_bmc = []
        result_ic3 = []

        proc_bmc = Thread(target=self.bmc.prove, args=(result_bmc,))
        proc_ic3 = Thread(target=self.ic3.prove, args=(result_ic3,))

        stop_bmc.clear()
        stop_ic3.clear()

        start_time = time.time()

        proc_bmc.start()
        proc_ic3.start()

        proc_bmc.join(timeout=timeout)
        proc_ic3.join(timeout=timeout)

        execution_time = time.time() - start_time

        if len(result_bmc) >= 1:
            return result_bmc[0], result_bmc[1], execution_time

        if len(result_ic3) >= 1:
            return not result_ic3[0], None, execution_time

        return None, None, execution_time


if __name__ == '__main__':

    if len(sys.argv) < 3:
        exit("Argument missing: ./parallelizer.py <places_to_reach> <path_to_Petri_net> [<path_to_reduced_Petri_net>]")

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
    sat, _, _ = parallelizer.run()
    print(formula.result(sat))
