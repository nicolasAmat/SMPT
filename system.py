#!/usr/bin/env python3

"""
Reduction Equations Module

Equations provided by the `reduce` tool.
Input file format: .net

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

import re
import sys

from pn import PetriNet


class System:
    """
    Equation system defined by:
    - a list of places from the initial Petri Net,
    - a list of places from the reduced Petri Net,
    - a list of additional variables,
    - a list of (in)equations.
    """

    def __init__(self, filename, places=[], places_reduced=[]):
        """ Initializer.
        """
        self.places = places
        self.places_reduced = places_reduced
        self.additional_vars = []

        self.equations = []
        self.parser(filename)

    def __str__(self):
        """ Equations to `reduce` tool format.
        """
        return '\n'.join(map(str, self.equations))

    def smtlib(self):
        """ Decalare additional variables
            and assert equations.
            
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var)
        for eq in self.equations:
            smt_input += eq.smtlib() + '\n'
        return smt_input

    def smtlib_only_non_reduced_places(self, k_initial=None):
        """ Declare additional variables
            and assert equations not involving places in the reduced net.
            
            k_initial: used by IC3.
            
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            if var not in self.places_reduced:
                var_name = var if k_initial is None else "{}@{}".format(var, k_initial)
                smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var_name, var_name)
        for eq in self.equations:
            if not eq.contain_reduced:
                smt_input += eq.smtlib(k_initial, [*self.places] + self.additional_vars) + '\n'
        return smt_input

    def smtlib_ordered(self, k, k_initial=None):
        """ Assert equations involving places in the reduced net.

            k:         used by BMC and IC3,
            k_initial: used by IC3.
            
            SMT-LIB format
        """
        smt_input = ""
        for eq in self.equations:
            if eq.contain_reduced:
                smt_input += eq.smtlib_ordered(k, k_initial, self.places_reduced,
                                               [*self.places] + self.additional_vars) + '\n'
        for pl in self.places_reduced:
            if pl in self.places:
                if k_initial is None:
                    smt_input += "(assert (= {}@{} {}))\n".format(pl, k, pl)
                else:
                    smt_input += "(assert (= {}@{} {}@{}))\n".format(pl, k, pl, k_initial)
        return smt_input

    def parser(self, filename):
        """ System of reduction equations parser.
            
            Input format: .net (output of the `reduce` tool)
        """
        try:
            with open(filename, 'r') as fp:
                content = re.search(r'# generated equations\n(.*)?\n\n', fp.read(), re.DOTALL)
                if content:
                    lines = re.split('\n+', content.group())[1:-1]
                    equations = [re.split(r'\s+', line.partition(' |- ')[2]) for line in lines]
                    for eq in equations:
                        self.equations.append(Equation(eq, self))
            fp.close()
        except FileNotFoundError as e:
            exit(e)


class Equation:
    """
    Equation defined by:
    - Left member,
    - Right member,
    - Operator.
    """

    def __init__(self, eq, system):
        """ Initializer.
        """
        self.left = []
        self.right = []
        self.operator = ""
        
        self.contain_reduced = False
        
        self.parse_equation(eq, system)

    def __str__(self):
        """ Equation to .net format.
        """
        return self.member_str(self.left) + '= ' + self.member_str(self.right)

    def member_str(self, member):
        """ Member to .net format.
        """
        text = ""
        for index, elem in enumerate(member):
            text += elem + " "
            if index != len(member) - 1:
                text += '+ '
        return text

    def smtlib(self, k_initial=None, other_vars=[]):
        """ Equation.

            SMT-LIB format
        """
        return "(assert ({}".format(self.operator) \
               + self.member_smtlib(self.left, k_initial, other_vars) \
               + self.member_smtlib(self.right, k_initial, other_vars) \
               + "))"

    def member_smtlib(self, member, k_initial, other_vars):
        """ Member.

            SMT-LIB format
        """
        smt_input = ""
        if len(member) > 1:
            smt_input += " (+"
        for elem in member:
            if k_initial is None or elem not in other_vars:
                smt_input += " {}".format(elem)
            else:
                smt_input += " {}@{}".format(elem, k_initial)
        if len(member) > 1:
            smt_input += ")"
        return smt_input

    def smtlib_ordered(self, k, k_initial, places_reduced, other_vars=[]):
        """ Equation with orders.

            k:              used by BMC and IC3
            k_initial:      used by IC3
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and initial net
            
            SMTLIB format
        """
        return "(assert ({}".format(self.operator) \
               + self.member_smtlib_ordered(self.left, k, k_initial, places_reduced, other_vars) \
               + self.member_smtlib_ordered(self.right, k, k_initial, places_reduced, other_vars) \
               + "))"

    def member_smtlib_ordered(self, member, k, k_initial, places_reduced=[], other_vars=[]):
        """ Equation with orders.

            k:              used by BMC and IC3
            k_initial:      used by IC3
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and initial net
            
            SMTLIB format
        """
        smt_input = ""
        if len(member) > 1:
            smt_input += " (+"
        for elem in member:
            if elem in places_reduced:
                smt_input += " {}@{}".format(elem, k)
            elif k_initial is not None and elem in other_vars:
                smt_input += " {}@{}".format(elem, k_initial)
            else:
                smt_input += " {}".format(elem)
        if len(member) > 1:
            smt_input += ")"
        return smt_input

    def parse_equation(self, eq, system):
        """ Equation parser.
            
            Input format: .net (output of the `reduced` tool)
        """
        for index, element in enumerate(eq):
            if element != '+':
                if element in ['=', '<=', '>=', '<', '>']:
                    self.operator = element
                else:
                    element = element.replace('{', '').replace('}', '').replace('#', '')
                    self.check_variable(element, system)
                    if index == 0:
                        self.left.append(element)
                    else:
                        self.right.append(element)

    def check_variable(self, element, system):
        """ Check if a given element is an additional variable and a place from the reduced net.
        """
        if not element.isnumeric():
            if element not in system.places and element not in system.additional_vars:
                system.additional_vars.append(element)
            if element in system.places_reduced:
                self.contain_reduced = True


if __name__ == "__main__":

    if len(sys.argv) < 3:
        exit("File missing: ./eq <path_to_initial_net> <path_to_reduced_net>")

    pn = PetriNet(sys.argv[1])
    pn_reduced = PetriNet(sys.argv[2])

    eq = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())

    print("Equations")
    print("---------")
    print(eq)

    print("\nSMTlib2 Format")
    print("--------------")
    print(eq.smtlib())
