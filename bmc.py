#!/usr/bin/env python3

"""
BMC (Bounded Model Checking)

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

import logging as log
import sys
from threading import Event, Thread

from pn import PetriNet
from properties import Properties
from solver import Solver
from system import System

stop_bmc = Event()


class BMC:
    """
    Bounded Model Checking method
    """
    def __init__(self, pn, formula, pn_reduced=None, eq=None, debug=False, stop_concurrent=None):
        """ BMC initializer.
        """
        self.pn = pn
        self.pn_reduced = pn_reduced
        
        self.eq = eq
        
        self.formula = formula
        self.R = formula.R
        
        self.solver = Solver(debug)

        self.stop_concurrent = stop_concurrent

    def smtlib(self, k):
        """ Return SMT-LIB format for understanding.
        """
        if self.pn_reduced is None:
            text = self.smtlib_without_reduction(k)
        else:
            text = self.smtlib_with_reduction(k)
        text += "(check-sat)\n(get-model)\n"
        return text

    def smtlib_without_reduction(self, k):
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
        text += self.R.smtlib(k + 1, assertion=True)

        return text

    def smtlib_with_reduction(self, k):
        """ Return SMT-LIB format for understanding.
        """
        text = ""

        text += "; Declaration of the places from the initial Petri Net\n"
        text += self.pn.smtlib_declare_places()

        text += "; Declaration of the additional variables\n"
        text += self.eq.smtlib_declare_additional_variables()

        text += "; Formula to check the satisfiability\n"
        text += self.R.smtlib(assertion=True)

        text += "; Reduction Equations (not involving places from the reduced Petri Net)"
        text += self.eq.smtlib_equations_without_places_from_reduced_net()

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
        text += self.eq.smtlib_equations_with_places_from_reduced_net(k)

        text == "; Link initial and reduced nets\n"
        text += self.eq.smtlib_link_nets(k)

        return text

    def prove(self, display=True, result=None):
        """ Prover.
        """
        log.info("---BMC RUNNING---")
        
        if self.pn_reduced is None:
            k = self.prove_without_reduction()
            order = k
        else:
            k = self.prove_with_reduction()
            order = None
        
        model = None
        
        if not stop_bmc.is_set():
            self.formula.result(True)
            if display:
                self.solver.display_model(self.pn, order)
            else:
                model = self.solver.get_model(self.pn, order)
        else:
            self.formula.result(False)

        self.solver.exit()
        
        if self.stop_concurrent:
            self.stop_concurrent.set()
        
        if result is not None:
            result.append(model)

        return model

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri Net.
        """
        log.info("[BMC] > Initialization")
        log.info("[BMC] \t>> Declaration of the places from the Petri Net (order: 0)")
        self.solver.write(self.pn.smtlib_declare_places(0))
        log.info("[BMC] \t>> Inital Marking of the Petri Net")
        self.solver.write(self.pn.smtlib_set_marking(0))
        log.info("[BMC] \t>> Push")
        self.solver.push()
        log.info("[BMC] \t>> Formula to check the satisfiability (order: 0)")
        self.solver.write(self.R.smtlib(0, assertion=True))
        
        k = 0
        while not self.solver.check_sat() and not stop_bmc.is_set():
            log.info("[BMC] > k = {}".format(k))
            log.info("[BMC] \t>> Pop")
            self.solver.pop()
            log.info("[BMC] \t>> Declaration of the places from the Petri Net (order: {})".format(k + 1))
            self.solver.write(self.pn.smtlib_declare_places(k + 1))
            log.info("[BMC] \t>> Transition Relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.pn.smtlib_transitions(k))
            log.info("[BMC] \t>> Push")
            self.solver.push()
            log.info("[BMC] \t>> Formula to check the satisfiability (order: {})".format(k + 1))
            self.solver.write(self.R.smtlib(k + 1, assertion=True))
            k += 1

        return k

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        log.info("[BMC] > Initialization")
        log.info("[BMC] \t>> Declaration of the places from the initial Petri Net")
        self.solver.write(self.pn.smtlib_declare_places())
        log.info("[BMC] \t>> Declaration of the additional variables")
        self.solver.write(self.eq.smtlib_declare_additional_variables())
        log.info("[BMC] \t>> Formula to check the satisfiability")
        self.solver.write(self.R.smtlib(assertion=True))
        log.info("[BMC] \t>> Reduction Equations (not involving places from the reduced Petri Net)")
        self.solver.write(self.eq.smtlib_equations_without_places_from_reduced_net())
        log.info("[BMC] \t>> Declaration of the places from the reduced Petri Net (order: 0)")
        self.solver.write(self.pn_reduced.smtlib_declare_places(0))
        log.info("[BMC] \t>> Inital Marking of the reduced Petri Net")
        self.solver.write(self.pn_reduced.smtlib_set_marking(0))
        log.info("[BMC] \t>> Push")
        self.solver.push()
        log.info("[BMC] \t>> Reduction Equations")
        self.solver.write(self.eq.smtlib_equations_with_places_from_reduced_net(0))
        log.info("[BMC] \t>> Link initial and reduced nets")
        self.solver.write(self.eq.smtlib_link_nets(0))
        
        k = 0
        while not self.solver.check_sat() and not stop_bmc.is_set():
            log.info("[BMC] > k = {}".format(k))
            log.info("[BMC] \t>> Pop")
            self.solver.pop()
            log.info("[BMC] \t>> Declaration of the places from the reduced Petri Net (order: {})".format(k + 1))
            self.solver.write(self.pn_reduced.smtlib_declare_places(k + 1))
            log.info("[BMC] \t>> Transition Relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.pn_reduced.smtlib_transitions(k))
            log.info("[BMC] \t>> Push")
            self.solver.push()
            log.info("[BMC] \t>> Reduction Equations")
            self.solver.write(self.eq.smtlib_equations_with_places_from_reduced_net(k + 1))
            log.info("[BMC] \t>> Link initial and reduced nets")
            self.solver.write(self.eq.smtlib_link_nets(k + 1))
            k += 1

        return k


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./bmc.py <path_to_initial_petri_net> [<path_to_reduce_net>]")
    
    log.basicConfig(format="%(message)s", level=log.DEBUG)

    pn = PetriNet(sys.argv[1])
    
    properties = Properties(pn)
    properties.generate_deadlock()
    formula = list(properties.formulas.values())[0]

    if len(sys.argv) == 3:
        pn_reduced = PetriNet(sys.argv[2])
        system = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = None
        system = None

    bmc = BMC(pn, formula, pn_reduced, system)

    print("> Input into the SMT Solver")
    print("---------------------------")
    print(bmc.smtlib(1))

    print("> Result computed using z3")
    print("--------------------------")
    proc = Thread(target= bmc.prove)
    proc.start()
    proc.join(timeout = 600)
    stop_bmc.set()
