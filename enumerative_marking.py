#!/usr/bin/env python3

"""
Enumerative Marking Module

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
__version__ = "1.0.0"

import logging as log
import re
import sys

from eq import System
from formula import Properties
from pn import PetriNet
from solver import Solver


class EnumerativeMarking:
    """
    Marking defined by:
    - a Petri Net,
    - a set of reachable markings.
    """
    def __init__(self, filename, pn, formula, pn_reduced, eq, debug=False):
        self.pn = pn
        self.formula = formula
        self.pn_reduced = pn_reduced
        self.eq = eq
        self.markings = []
        self.parse_markings(filename)
        self.solver = Solver(debug)

    def __str__(self):
        """ Str method for markings.
        """
        text = ""
        for marking in self.markings:
            text += "-> "
            for place, counter in marking.items():
                text += "{}:{} ".format(place, counter)
            text += "\n"
        return text

    def smtlib(self):
        """ Return SMT-LIB assertions for markings (DNF).
        """
        text = ""
        if self.pn_reduced is None:
            places = self.pn.places
        else:
            places = self.pn_reduced.places
        text += "(assert (or "
        for marking in self.markings:
            text += "(and "
            for place, counter in marking.items():
                text += "(= {} {})". format(place, counter)
            for place in places:
                if place not in marking:
                    text += "(= {} 0)". format(place)
            text += ")"
        text += "))\n"
        return text

    def parse_markings(self, filename):
        """ Parse markings (.aut file format).
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = line.strip().replace('(', '').replace(')', '').split(',')
                    if content[0] == content[-1]:
                        places = re.split(r'\s+', content[1].replace('"', ''))
                        consistent = True
                        marking = dict()
                        for place in places:
                            place_data = place.split('.')
                            if place_data[0] != 'S':
                                consistent = False
                                break
                            marking[place_data[1].replace('`', '').replace('{', '').replace('}', '')] = 1
                        if consistent:
                            self.markings.append(marking)
        except FileNotFoundError as e:
            exit(e)

    def prove(self):
        """ Prover.
        """
        print("---ENUMERATIVE MARKING RUNNING---")

        if self.pn_reduced is None:
            self.prove_non_reduced()
        else:
            self.prove_reduced()

        if self.solver.check_sat():
            self.formula.result(True)
            self.solver.display_model(self.pn)
        else:
            self.formula.result(False)

        self.solver.exit()

    def prove_non_reduced(self):
        """ Prover for non-reduced Petri net.
        """
        log.info("> Variable Definitions")
        self.solver.write(self.pn.smtlib_declare_places())
        log.info("> Property Formula")
        self.solver.write(self.formula.smtlib())
        log.info("> Net Markings")
        self.solver.write(self.smtlib())

    def prove_reduced(self):
        """ Prover for reduced Petri net.
        """
        log.info("> Variable Definitions")
        self.solver.write(self.pn.smtlib_declare_places())
        log.info("> Reduction Equations")
        self.solver.write(self.eq.smtlib())
        log.info("> Property Formula")
        self.solver.write(self.formula.smtlib())
        log.info("> Reduced Net Markings")
        self.solver.write(self.smtlib())


if __name__ == '__main__':

    if len(sys.argv) != 3:
        exit("File missing: ./enumerative_marking <path_to_net_file> <path_to_aut_file>")

    net = PetriNet(sys.argv[1])
    markings = EnumerativeMarking(sys.argv[2], net, None, None, None)

    print("Markings Enumeration")
    print("--------------------")
    print(markings)

    print("\nSMTlib2 Format")
    print("--------------")
    print(markings.smtlib())
