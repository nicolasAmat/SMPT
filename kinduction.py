#!/usr/bin/env python3

"""
k-induction
"""

from pn import PetriNet
from eq import System
from formula import Formula
from solver import Solver

import sys
from threading import Thread, Event
import logging as log

stop_it = Event()


class KInduction:
    """
    K-induction method
    """
    def __init__(self, pn, pn_reduced, eq, formula):
        """K-induction initializer."""
        self.pn = pn
        self.pn_reduced = pn_reduced
        self.eq = eq
        self.formula = formula
        self.solver = Solver()

    def smtlib_ordered(self, k):
        """Return SMT-LIB format for understanding."""
        text = ""

        text += "; Declaration of the places from the original Petri Net\n"
        text += self.pn.smtlib_declare_places()

        text += "; Formula to check the satisfiability\n"
        text += self.formula.smtlib()

        text += "; Reduction Equations"
        text += self.eq.smtlib_only_non_reduced_places()

        text += "; Declaration of the places from the reduced Petri Net (order: {})\n".format(0)
        text += self.pn_reduced.smtlib_declare_places_ordered(0)

        text += "; Inital Marking of the reduced Petri Net\n"
        text += self.pn_reduced.smtlib_set_marking_ordered(0)

        for i in range(k):
            text += "; Declaration of the places from the reduced Petri Net (order: {})\n".format(1)
            text += self.pn_reduced.smtlib_declare_places_ordered(i + 1)

            text += "; Transition Relation: {} -> {}\n".format(i, i + 1)
            text += self.pn_reduced.smtlib_transitions_ordered(i)

        text += "; Reduction Equations\n"
        text += self.eq.smtlib_ordered(k)

        text += "(check-sat)\n(get-model)\n"

        return text

    def prove(self):
        """Prover."""
        print("---K-INDUCTION RUNNING---")

        log.info("> Initialization")
        log.info("\t>> Declaration of the places from the original Petri Net")
        self.solver.write(self.pn.smtlib_declare_places())
        log.info("\t>> Formula to check the satisfiability")
        self.solver.write(self.formula.smtlib())
        log.info("\t>> Reduction Equations (not involving places from the reduced Petri Net)")
        self.solver.write(self.eq.smtlib_only_non_reduced_places())
        log.info("\t>> Declaration of the places from the reduced Petri Net (order : 0)")
        self.solver.write(self.pn_reduced.smtlib_declare_places_ordered(0))
        log.info("\t>> Inital Marking of the reduced Petri Net")
        self.solver.write(self.pn_reduced.smtlib_set_marking_ordered(0))
        log.info("\t>> Push")
        self.solver.push()
        log.info("\t>> Reduction Equations")
        self.solver.write(self.eq.smtlib_ordered(0))
        
        k = 0
        while k < 100 and not self.solver.check_sat() and not stop_it.is_set():
            log.info("> k = {}".format(k))
            log.info("\t>> Pop")
            self.solver.pop()
            log.info("\t>> Declaration of the places from the reduced Petri Net (order: {})".format(k + 1))
            self.solver.write(self.pn_reduced.smtlib_declare_places_ordered(k + 1))
            log.info("\t>> Transition Relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.pn_reduced.smtlib_transitions_ordered(k))
            log.info("\t>> Pop")
            self.solver.push()
            self.solver.write(self.eq.smtlib_ordered(k + 1))
            k += 1
        
        print()
        if k < 100 and not stop_it.is_set():
            self.formula.result(True)
            self.solver.display_model(self.pn)
        else:
            print("Method stopped.")
            self.formula.result(False)

        self.solver.exit()


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./kinduction.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    
    if len(sys.argv) == 3:
        pn_reduced = PetriNet(sys.argv[2])
        system = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = PetriNet(sys.argv[1])
        system = System(sys.argv[1], pn.places.keys(), pn_reduced.places.keys())
    
    formula = Formula(pn)
    
    k_induction = KInduction(pn, pn_reduced, system, formula)

    print("Input into the SMT Solver")
    print("-------------------------")
    print(k_induction.smtlib_ordered(1))

    print("Result computed using z3")
    print("------------------------")
    proc = Thread(target= k_induction.prove)
    proc.start()
    proc.join(timeout = 600)
    stop_it.set()
