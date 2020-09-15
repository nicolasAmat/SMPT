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
from pn import PetriNet
from properties import Properties
from system import System


class Parallelizer:
    """ Concurrent analyzer.
    """

    def __init__(self, pn, formula, pn_reduced=None, eq=None, debug=False):
        """ Initializer.
        """
        self.bmc = BMC(pn, formula, pn_reduced=pn_reduced, eq=eq, debug=debug, stop_concurrent=stop_ic3)
        self.ic3 = IC3(pn, formula, pn_reduced=pn_reduced, eq=eq, debug=debug, stop_concurrent=stop_bmc)

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
        exit("File missing: ./parallelizer.py <places_to_reach> <path_to_Petri_net> [<path_to_reduced_Petri_net>]")

    pn = PetriNet(sys.argv[2])
    marking = {pn.places[pl]: 1 for pl in sys.argv[1].split(',')}

    properties = Properties(pn)
    properties.generate_reachability(marking)
    formula = list(properties.formulas.values())[0]

    if len(sys.argv) == 4:
        pn_reduced = PetriNet(sys.argv[3])
        eq = System(sys.argv[3], pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = None
        eq = None

    parallelizer = Parallelizer(pn, formula, pn_reduced, eq)

    print("> Result of the parallelized analysis")
    print("-------------------------------------")
    parallelizer.run()
