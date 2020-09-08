#!/usr/bin/env python3

"""
Parallelizer for IC3 and k-induction analysis methods.

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
__version__ = "1.0.0"

import sys
from threading import Event, Thread

from eq import System
from formula import Formula
from ic3 import IC3, stop_ic3
from k_induction import KInduction, stop_k_induction
from pn import PetriNet


class Parallelizer:
    """ Concurrent analyzer.
    """

    def __init__(self, pn, formula, pn_reduced=None, eq=None, debug=False):
        """ Initializer.
        """
        self.ic3 = IC3(pn, formula, pn_reduced=pn_reduced, eq=eq, debug=debug, stop_concurrent=stop_k_induction)
        self.k_induction = KInduction(pn, formula, pn_reduced=pn_reduced, eq=eq, debug=debug, stop_concurrent=stop_ic3)

    def run(self):
        """ Run IC3 and k-induction analysis in parrallel.

            Return `True` is the property is verified,
            Return a counterexample otherwise.
        """
        result_ic3 = []
        result_k_induction = []

        proc_ic3 = Thread(target=self.ic3.prove, args=(result_ic3,))
        proc_k_induction = Thread(target=self.k_induction.prove, args=(False, result_k_induction,))

        stop_ic3.clear()
        stop_k_induction.clear()

        proc_ic3.start()
        proc_k_induction.start()

        proc_ic3.join()
        proc_k_induction.join()

        if len(result_ic3) == 1:
            return True
        else:
            return result_k_induction[0]


if __name__ == '__main__':

    if len(sys.argv) < 2:
        exit("File missing: ./parallelizer.py <place_to_reach> <path_to_petri_net> [<path_to_reduced_petri_net>]")

    pn = PetriNet(sys.argv[2])
    marking = {pn.places[sys.argv[1]]: 1}
    formula = Formula(pn, prop='reachability', marking=marking)

    if len(sys.argv) == 4:
        pn_reduced = PetriNet(sys.argv[3])
        eq = System(sys.argv[3], pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = None
        eq = None

    parallelizer = Parallelizer(pn, formula, pn_reduced, eq)

    print("Result of the parallelized analysis")
    print("-----------------------------------")
    print(parallelizer.run())
