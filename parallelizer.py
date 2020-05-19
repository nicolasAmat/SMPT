#!/usr/bin/env python3

"""
Parallelizer for IC3 and k-induction analysis methods.
"""

from pn import PetriNet
from formula import Formula
from eq import System
from ic3 import IC3
from k_induction import KInduction, stop_it

import sys
from threading import Thread, Event

stop_ic3 = Event()
stop_k_induction = Event()


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
        
        proc_ic3 =  Thread(target=self.ic3.prove, args=(result_ic3,))
        proc_k_induction = Thread(target=self.k_induction.prove, args=(False, result_k_induction,))

        proc_ic3.start()
        proc_k_induction.start()

        proc_ic3.join()
        proc_k_induction.join()


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./parallelizer.py <place_to_reach> <path_to_petri_net> [<path_to_reduced_petri_net>]")
    
    pn = PetriNet(sys.argv[2])
    marking = {pn.places[sys.argv[1]] : 1}
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
