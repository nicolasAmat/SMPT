#!/usr/bin/env python3

"""
k-induction
"""

from pn import PetriNet
from eq import System
from formula import Formula
from solver import Solver

import sys
import logging as log
from threading import Thread, Event

stop_it = Event()


class KInduction:
    """
    K-induction method
    """
    def __init__(self, pn, formula, pn_reduced=None, eq=None, debug=False, stop_concurrent=None):
        """ K-induction initializer.
        """
        self.pn = pn
        self.formula = formula
        self.pn_reduced = pn_reduced
        self.eq = eq
        self.solver = Solver(debug)

        self.stop_concurrent = stop_concurrent

    def smtlib(self, k):
        """ Return SMT-LIB format for understanding.
        """
        if self.pn_reduced is None:
            text = self.smtlib_non_reduced(k)
        else:
            text = self.smtlib_reduced(k)
        text += "(check-sat)\n(get-model)\n"
        return text

    def smtlib_non_reduced(self, k):
        """ Return SMT-LIB format for understanding.
        """
        text = ""

        text += "; Declaration of the places from the Petri Net(order: {})\n".format(0)
        text += self.pn.smtlib_declare_places(0)

        text += "; Inital Marking of the Petri Net\n"
        text += self.pn.smtlib_set_marking(0)

        for i in range(k):
            text += "; Declaration of the places from the Petri Net (order: {})\n".format(1)
            text += self.pn.smtlib_declare_places(i + 1)

            text += "; Transition Relation: {} -> {}\n".format(i, i + 1)
            text += self.pn.smtlib_transitions(i)

        text += "; Formula to check the satisfiability\n"
        text += self.formula.smtlib(k + 1)

        return text

    def smtlib_reduced(self, k):
        """ Return SMT-LIB format for understanding.
        """
        text = ""

        text += "; Declaration of the places from the original Petri Net\n"
        text += self.pn.smtlib_declare_places()

        text += "; Formula to check the satisfiability\n"
        text += self.formula.smtlib()

        text += "; Reduction Equations (not involving places from the reduced Petri Net)"
        text += self.eq.smtlib_only_non_reduced_places()

        text += "; Declaration of the places from the reduced Petri Net (order: {})\n".format(0)
        text += self.pn_reduced.smtlib_declare_places(0)

        text += "; Inital Marking of the reduced Petri Net\n"
        text += self.pn_reduced.smtlib_set_marking(0)

        for i in range(k):
            text += "; Declaration of the places from the reduced Petri Net (order: {})\n".format(1)
            text += self.pn_reduced.smtlib_declare_places(i + 1)

            text += "; Transition Relation: {} -> {}\n".format(i, i + 1)
            text += self.pn_reduced.smtlib_transitions(i)

        text += "; Reduction Equations\n"
        text += self.eq.smtlib_ordered(k)

        return text

    def prove(self, display=True, result=None):
        """ Prover.
        """
        log.info("---K-INDUCTION RUNNING---")
        
        if self.pn_reduced is None:
            k = self.prove_non_reduced()
            order = k
        else:
            k = self.prove_reduced()
            order = None
        
        model = None
        
        if k < 100 and not stop_it.is_set():
            self.formula.result(True)
            if display:
                self.solver.display_model(self.pn, order)
            else:
                model = self.solver.get_model(self.pn, order)
        else:
            print("Method stopped.")
            self.formula.result(False)

        self.solver.exit()
        
        if self.stop_concurrent:
            self.stop_concurrent.set()
        if result is not None:
            result.append(model)

        return model

    def prove_non_reduced(self):
        """ Prover using the original Petri Net.
        """
        log.info("> Initialization")
        log.info("\t>> Declaration of the places from the Petri Net (order: 0)")
        self.solver.write(self.pn.smtlib_declare_places(0))
        log.info("\t>> Inital Marking of the Petri Net")
        self.solver.write(self.pn.smtlib_set_marking(0))
        log.info("\t>> Push")
        self.solver.push()
        log.info("\t>> Formula to check the satisfiability (order: 0)")
        self.solver.write(self.formula.smtlib(0))
        
        k = 0
        while k < 100 and not self.solver.check_sat() and not stop_it.is_set():
            log.info("> k = {}".format(k))
            log.info("\t>> Pop")
            self.solver.pop()
            log.info("\t>> Declaration of the places from the Petri Net (order: {})".format(k + 1))
            self.solver.write(self.pn.smtlib_declare_places(k + 1))
            log.info("\t>> Transition Relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.pn.smtlib_transitions(k))
            log.info("\t>> Push")
            self.solver.push()
            log.info("\t>> Formula to check the satisfiability (order: {})".format(k + 1))
            self.solver.write(self.formula.smtlib(k + 1))
            k += 1

        return k

    def prove_reduced(self):
        """ Prover using the reduced Petri Net.
        """
        log.info("> Initialization")
        log.info("\t>> Declaration of the places from the original Petri Net")
        self.solver.write(self.pn.smtlib_declare_places())
        log.info("\t>> Formula to check the satisfiability")
        self.solver.write(self.formula.smtlib())
        log.info("\t>> Reduction Equations (not involving places from the reduced Petri Net)")
        self.solver.write(self.eq.smtlib_only_non_reduced_places())
        log.info("\t>> Declaration of the places from the reduced Petri Net (order: 0)")
        self.solver.write(self.pn_reduced.smtlib_declare_places(0))
        log.info("\t>> Inital Marking of the reduced Petri Net")
        self.solver.write(self.pn_reduced.smtlib_set_marking(0))
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
            self.solver.write(self.pn_reduced.smtlib_declare_places(k + 1))
            log.info("\t>> Transition Relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.pn_reduced.smtlib_transitions(k))
            log.info("\t>> Push")
            self.solver.push()
            self.solver.write(self.eq.smtlib_ordered(k + 1))
            k += 1

        return k


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./k_induction.py <path_to_initial_petri_net> [<path_to_reduce_net>]")
    
    log.basicConfig(format="%(message)s", level=log.DEBUG)

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, prop='deadlock')
    
    if len(sys.argv) == 3:
        pn_reduced = PetriNet(sys.argv[2])
        eq = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = None
        eq = None

    k_induction = KInduction(pn, formula, pn_reduced, eq)

    print("Input into the SMT Solver")
    print("-------------------------")
    print(k_induction.smtlib(1))

    print("Result computed using z3")
    print("------------------------")
    proc = Thread(target= k_induction.prove)
    proc.start()
    proc.join(timeout = 600)
    stop_it.set()
