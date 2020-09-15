#!/usr/bin/env python3

"""
Enumerative Marking Method

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

from ptnet import PetriNet
from properties import Properties
from solver import Solver
from system import System


class Enumerative:
    """
    Marking defined by:
    - a Petri Net,
    - a set of reachable markings.
    """
    def __init__(self, filename, ptnet, formula, ptnet_reduced, system, debug=False):
        self.ptnet = ptnet
        self.ptnet_reduced = ptnet_reduced
        
        self.system = system
        
        self.formula = formula
        self.R = formula.R

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
        if self.ptnet_reduced is None:
            places = self.ptnet.places
        else:
            places = self.ptnet_reduced.places
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

        if self.ptnet_reduced is None:
            self.prove_without_reduction()
        else:
            self.prove_with_reduction()

        if self.solver.check_sat():
            self.formula.result(True)
            self.solver.display_model(self.ptnet)
        else:
            self.formula.result(False)

        self.solver.exit()

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri net.
        """
        log.info("> Variable Definitions")
        self.solver.write(self.ptnet.smtlib_declare_places())
        log.info("> Property Formula")
        self.solver.write(self.R.smtlib(assertion=True))
        log.info("> Net Markings")
        self.solver.write(self.smtlib())

    def prove_with_reduction(self):
        """ Prover for reduced Petri net.
        """
        log.info("> Variable Definitions")
        self.solver.write(self.ptnet.smtlib_declare_places())
        log.info("> Reduction Equations")
        self.solver.write(self.system.smtlib())
        log.info("> Property Formula")
        self.solver.write(self.R.smtlib(assertion=True))
        log.info("> Reduced Net Markings")
        self.solver.write(self.smtlib())


if __name__ == '__main__':

    if len(sys.argv) != 3:
        exit("File missing: ./enumerative.py <path_to_net_file> <path_to_aut_file>")

    ptnet = PetriNet(sys.argv[1])
    markings = Enumerative(sys.argv[2], ptnet, None, None, None)

    print("> Markings Enumeration")
    print("----------------------")
    print(markings)

    print("> SMTlib2 Format")
    print("----------------")
    print(markings.smtlib())
