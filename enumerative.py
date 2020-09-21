#!/usr/bin/env python3

"""
Enumerative markings method

Input file format: .aut
Documentation: http://projects.laas.fr/tina//manuals/formats.html

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
import re
import sys

from properties import Formula
from ptnet import PetriNet
from solver import Solver
from system import System


class Enumerative:
    """ Enumerative markings method.
    """

    def __init__(self, filename, ptnet, formula, ptnet_reduced, system, debug=False):
        """ Initializer.
        """
        self.ptnet = ptnet
        self.ptnet_reduced = ptnet_reduced

        self.system = system

        self.formula = formula

        self.markings = []
        self.parse_markings(filename)

        self.solver = Solver(debug)

    def __str__(self):
        """ Markings to str.
        """
        text = ""
        for marking in self.markings:
            text += "->"
            for place, tokens in marking.items():
                text += " {}:{}".format(place, tokens)
            text += "\n"
        return text

    def smtlib(self):
        """ Assert markings (DNF).
            SMT-LIB format
        """
        if len(self.markings) == 0:
            return ""

        if self.ptnet_reduced is None:
            places = self.ptnet.places
        else:
            places = self.ptnet_reduced.places

        smt_input = "(assert (or "

        for marking in self.markings:
            smt_input += "(and "
            for place, tokens in marking.items():
                smt_input += "(= {} {})".format(place, tokens)
            for place in places:
                if place not in marking:
                    smt_input += "(= {} 0)".format(place)
            smt_input += ")"
        smt_input += "))\n"

        return smt_input

    def parse_markings(self, filename):
        """ Parse markings (.aut file format).
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = line.strip().replace('(', '').replace(')', '').split(',')
                    if len(content) >= 3 and content[0] == content[-1]:
                        content = re.split(r'\s+', content[1].replace('"', ''))
                        consistent = True
                        marking = dict()
                        for marking_data in content:
                            place_marking = marking_data.split('.')
                            if place_marking[0] != 'S':
                                consistent = False
                                break
                            place_marking = place_marking[1].split('*')
                            place_id = place_marking[0].replace('`', '').replace('{', '').replace('}', '')
                            if place_id == '':
                                consistent = False
                                break
                            if len(place_marking) > 1:
                                tokens = int(place_marking[1])
                            else:
                                tokens = 1
                            marking[place_id] = tokens
                        if consistent:
                            self.markings.append(marking)
        except FileNotFoundError as e:
            exit(e)

    def prove(self, result=[]):
        """ Prover.
        """
        log.info("[ENUMERATIVE] RUNNING")

        if self.ptnet_reduced is None:
            self.prove_without_reduction()
        else:
            self.prove_with_reduction()

        if self.solver.check_sat():
            result.append(True)
            result.append(self.solver.get_model(self.ptnet))
        else:
            result.append(False)

        self.solver.exit()

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri net.
        """
        log.info("[ENUMERATIVE] Declaration of the places")
        self.solver.write(self.ptnet.smtlib_declare_places())
        log.info("[ENUMERATIVE] Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))
        log.info("[ENUMERATIVE] Markings")
        self.solver.write(self.smtlib())

    def prove_with_reduction(self):
        """ Prover for reduced Petri net.
        """
        log.info("[ENUMERATIVE] Declaration of the places")
        self.solver.write(self.ptnet.smtlib_declare_places())
        log.info("[ENUMERATIVE] Reduction equations")
        self.solver.write(self.system.smtlib())
        log.info("[ENUMERATIVE] Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))
        log.info("[ENUMERATIVE] Markings from the reduced net")
        self.solver.write(self.smtlib())


if __name__ == '__main__':

    if len(sys.argv) < 3:
        exit("File missing: ./enumerative.py <path_to_Petri_net> <path_to_aut_file> [<path_to_reduced_net>]")

    log.basicConfig(format="%(message)s", level=log.DEBUG)

    ptnet = PetriNet(sys.argv[1])

    formula = Formula(ptnet)
    formula.generate_deadlock()

    if len(sys.argv) == 4:
        ptnet_reduced = PetriNet(sys.argv[3])
        system = System(sys.argv[3], ptnet.places.keys(), ptnet_reduced.places.keys())
    else:
        ptnet_reduced = None
        system = None

    enumerative = Enumerative(sys.argv[2], ptnet, formula, ptnet_reduced, system)

    print("> Markings enumeration")
    print("----------------------")
    print(enumerative)

    print("> Generated SMT-LIB")
    print("-------------------")
    print(enumerative.smtlib())

    print("> Result computed using z3")
    print("--------------------------")
    result = []
    enumerative.prove(result)
    formula.result(result[0])
    if len(result) > 1:
        result[1].display_model()
