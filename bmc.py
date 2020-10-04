#!/usr/bin/env python3

"""
BMC: Bounded Model Checking

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

import logging as log
import os
import signal
import sys
from multiprocessing import Process, Queue

import psutil

from properties import Formula
from ptnet import PetriNet
from solver import Solver
from system import System


class BMC:
    """
    Bounded Model Checking method.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False, parallelizer_pid=None):
        """ Initializer.
        """
        self.ptnet = ptnet
        self.ptnet_reduced = ptnet_reduced

        self.system = system

        self.formula = formula

        self.solver = Solver(debug)
        self.parallelizer_pid = parallelizer_pid

    def smtlib(self, k):
        """ SMT-LIB format for understanding.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction(k)
        else:
            smt_input = self.smtlib_with_reduction(k)

        smt_input += "(check-sat)\n(get-model)\n"

        return smt_input

    def smtlib_without_reduction(self, k):
        """ SMT-LIB format for understanding.
            Case without reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net (order: {})\n".format(0)
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Initial marking of the Petri net\n"
        smt_input += self.ptnet.smtlib_initial_marking(0)

        for i in range(k):
            smt_input += "; Declaration of the places from the Petri net (order: {})\n".format(1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet.smtlib_transition_relation(i)

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(k + 1, assertion=True)

        return smt_input

    def smtlib_with_reduction(self, k):
        """ SMT-LIB format for understanding.
            Case with reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the initial Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the additional variables\n"
        smt_input += self.system.smtlib_declare_additional_variables()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        smt_input += "; Reduction equations (not involving places from the reduced Petri net)"
        smt_input += self.system.smtlib_equations_without_places_from_reduced_net()

        smt_input += "; Declaration of the places from the reduced Petri net (order: {})\n".format(0)
        smt_input += self.ptnet_reduced.smtlib_declare_places(0)

        smt_input += "; Initial marking of the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_initial_marking(0)

        for i in range(k):
            smt_input += "; Declaration of the places from the reduced Petri net (order: {})\n".format(1)
            smt_input += self.ptnet_reduced.smtlib_declare_places(i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet_reduced.smtlib_transition_relation(i)

        smt_input += "; Reduction equations\n"
        smt_input += self.system.smtlib_equations_with_places_from_reduced_net(k)

        smt_input += "; Link initial and reduced Petri nets\n"
        smt_input += self.system.smtlib_link_nets(k)

        return smt_input

    def prove(self, result=[]):
        """ Prover.
        """
        log.info("[BMC] RUNNING")

        if self.ptnet_reduced is None:
            order = self.prove_without_reduction()
        else:
            self.prove_with_reduction()
            order = None

        # Put the result in the queue
        result.put([True, self.solver.get_model(self.ptnet, order)])

        # Kill parallelizer children
        if self.parallelizer_pid:
            bmc_pid = os.getpid()
            parent = psutil.Process(self.parallelizer_pid)
            children = parent.children(recursive=True)
            for process in children:
                if process.pid != bmc_pid:
                    process.send_signal(signal.SIGTERM)

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri Net.
        """
        log.info("[BMC] > Initialization")
        log.info("[BMC] \t>> Declaration of the places from the Petri net (order: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))
        log.info("[BMC] \t>> Initial marking of the Petri net")
        self.solver.write(self.ptnet.smtlib_initial_marking(0))
        log.info("[BMC] \t>> Push")
        self.solver.push()
        log.info("[BMC] \t>> Formula to check the satisfiability (order: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        k = 0
        while not self.solver.check_sat():
            log.info("[BMC] > k = {}".format(k))
            log.info("[BMC] \t>> Pop")
            self.solver.pop()
            log.info("[BMC] \t>> Declaration of the places from the Petri net (order: {})".format(k + 1))
            self.solver.write(self.ptnet.smtlib_declare_places(k + 1))
            log.info("[BMC] \t>> Transition relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.ptnet.smtlib_transition_relation(k))
            log.info("[BMC] \t>> Push")
            self.solver.push()
            log.info("[BMC] \t>> Formula to check the satisfiability (order: {})".format(k + 1))
            self.solver.write(self.formula.R.smtlib(k + 1, assertion=True))
            k += 1

        return k

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        log.info("[BMC] > Initialization")
        log.info("[BMC] \t>> Declaration of the places from the initial Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())
        log.info("[BMC] \t>> Declaration of the additional variables")
        self.solver.write(self.system.smtlib_declare_additional_variables())
        log.info("[BMC] \t>> Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))
        log.info("[BMC] \t>> Reduction equations (not involving places from the reduced Petri net)")
        self.solver.write(self.system.smtlib_equations_without_places_from_reduced_net())
        log.info("[BMC] \t>> Declaration of the places from the reduced Petri net (order: 0)")
        self.solver.write(self.ptnet_reduced.smtlib_declare_places(0))
        log.info("[BMC] \t>> Initial marking of the reduced Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_initial_marking(0))
        log.info("[BMC] \t>> Push")
        self.solver.push()
        log.info("[BMC] \t>> Reduction equations")
        self.solver.write(self.system.smtlib_equations_with_places_from_reduced_net(0))
        log.info("[BMC] \t>> Link initial and reduced Petri nets")
        self.solver.write(self.system.smtlib_link_nets(0))

        k = 0
        while not self.solver.check_sat():
            log.info("[BMC] > k = {}".format(k))
            log.info("[BMC] \t>> Pop")
            self.solver.pop()
            log.info("[BMC] \t>> Declaration of the places from the reduced Petri net (order: {})".format(k + 1))
            self.solver.write(self.ptnet_reduced.smtlib_declare_places(k + 1))
            log.info("[BMC] \t>> Transition relation: {} -> {}".format(k, k + 1))
            self.solver.write(self.ptnet_reduced.smtlib_transition_relation(k))
            log.info("[BMC] \t>> Push")
            self.solver.push()
            log.info("[BMC] \t>> Reduction equations")
            self.solver.write(self.system.smtlib_equations_with_places_from_reduced_net(k + 1))
            log.info("[BMC] \t>> Link initial and reduced Petri nets")
            self.solver.write(self.system.smtlib_link_nets(k + 1))
            k += 1

        return k


if __name__ == '__main__':

    if len(sys.argv) < 2:
        sys.exit("Argument missing: ./bmc.py <path_to_Petri_net> [<path_to_reduced_Petri_net>]")

    log.basicConfig(format="%(message)s", level=log.DEBUG)

    ptnet = PetriNet(sys.argv[1])

    formula = Formula(ptnet)
    formula.generate_deadlock()

    if len(sys.argv) == 3:
        ptnet_reduced = PetriNet(sys.argv[2])
        system = System(sys.argv[2], ptnet.places.keys(), ptnet_reduced.places.keys())
    else:
        ptnet_reduced = None
        system = None

    bmc = BMC(ptnet, formula, ptnet_reduced, system)

    print("> Generated SMT-LIB")
    print("-------------------")
    print(bmc.smtlib(1))

    print("> Result computed using z3")
    print("--------------------------")
    result = Queue()
    proc = Process(target=bmc.prove, args=(result,))
    proc.start()
    proc.join(timeout=60)
    if not result.empty():
        sat, model = result.get()
        print(formula.result(sat))
        model.display_model()

