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
from threading import Event, Thread

from bmc import BMC, stop_bmc
from ic3 import IC3, stop_ic3
from properties import Formula
from ptnet import PetriNet
from system import System


class Parallelizer:
    """ Concurrent analyzer.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False):
        """ Initializer.
        """
        self.bmc = BMC(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug, stop_concurrent=stop_ic3)
        self.ic3 = IC3(ptnet, formula, ptnet_reduced=ptnet_reduced, system=system, debug=debug, stop_concurrent=stop_bmc)

    def run(self):
        """ Run BMC and IC3 analysis in parrallel.

            Return `True` is the property is verified,
            Return a counterexample otherwise.
        """
        result_bmc = []
        result_ic3 = []

        proc_bmc = Thread(target=self.bmc.prove, args=(False, result_bmc,))
        proc_ic3 = Thread(target=self.ic3.prove, args=(result_ic3,))

        stop_bmc.clear()
        stop_ic3.clear()

        proc_bmc.start()
        proc_ic3.start()

        proc_bmc.join()
        proc_ic3.join()

        if len(result_ic3) == 1:
            return True
        else:
            return result_bmc[0]


if __name__ == '__main__':

    if len(sys.argv) < 2:
        exit("File missing: ./parallelizer.py <path_to_Petri_net> [<path_to_reduced_Petri_net>]")

    ptnet = PetriNet(sys.argv[1])

    formula = Formula(ptnet)
    formula.generate_deadlock()

    if len(sys.argv) == 3:
        ptnet_reduced = PetriNet(sys.argv[2])
        system = System(sys.argv[2], ptnet.places.keys(), ptnet_reduced.places.keys())
    else:
        ptnet_reduced = None
        system = None

    parallelizer = Parallelizer(ptnet, formula, ptnet_reduced, system)

    print("> Result of the parallelized analysis")
    print("-------------------------------------")
    parallelizer.run()
