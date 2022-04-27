#!/usr/bin/env python3

"""
Reduction Equations Module

Equations provided by the `reduce` tool from the TINA toolbox.
TINA toolbox: http://projects.laas.fr/tina/

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

import re
import sys

from ptnet import PetriNet


class System:
    """
    Equation system defined by:
    - a list of places from the initial Petri net,
    - a list of places from the reduced Petri net,
    - a list of additional variables,
    - a list of (in)equations.
    """

    def __init__(self, filename, places_initial=None, places_reduced=None):
        """ Initializer.
        """
        if places_initial is None:
            places_initial = []
        self.places_initial = places_initial

        if places_reduced is None:
            places_reduced = []
        self.places_reduced = places_reduced

        self.additional_vars = []

        self.equations = []

        self.parser(filename)

    def __str__(self):
        """ Equations to `reduce` tool format.
        """
        return '\n'.join(map(str, self.equations))

    def smtlib(self, k=None, k_initial=None):
        """ Decalare additional variables and assert equations.
            SMT-LIB format
        """
        if k is None:
            smt_input = ''.join(
                map(lambda var: "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var), self.additional_vars))
        else:
            smt_input = ''.join(
                map(lambda var: "(declare-const {}@{} Int)\n(assert (>= {}@{} 0))\n".format(var, k, var, k), self.additional_vars))

        if k is None and k_initial is None:
            smt_input += '\n'.join(map(lambda eq: eq.smtlib(), self.equations)) + '\n'
        else:
            smt_input += '\n'.join(map(lambda eq: eq.smtlib_with_order(k, k_initial, self.places_reduced, [*self.places_initial] + self.additional_vars), self.equations)) + '\n'

        return smt_input

    def minizinc(self):
        """ Declare additional variables and assert equations.
            SMT-LIB format
        """
        minizinc_input = ""

        for var in self.additional_vars:
            if var not in self.places_reduced:
                minizinc_input += "var 0..MAX: {};\n".format(var)

        minizinc_input += ''.join(map(lambda eq: eq.minizinc(), self.equations))

        return minizinc_input

    def smtlib_declare_additional_variables(self, k_initial=None):
        """ Declare additional variables.

            k_initial: used by PDR.

            SMT-LIB format
        """
        smt_input = ""

        for var in self.additional_vars:
            if var not in self.places_reduced:
                var_name = var if k_initial is None else "{}@{}".format(var, k_initial)
                smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var_name, var_name)

        return smt_input

    def smtlib_equations_without_places_from_reduced_net(self, k_initial=None):
        """ Assert equations not involving places in the reduced net.

            k_initial: used by PDR.

            SMT-LIB format
        """
        smt_input = ""

        for eq in self.equations:
            if not eq.contain_reduced:
                smt_input += eq.smtlib(k_initial, [*self.places_initial] + self.additional_vars) + '\n'

        return smt_input

    def smtlib_equations_with_places_from_reduced_net(self, k, k_initial=None):
        """ Assert equations involving places in the reduced net.

            k:         used by BMC and PDR,
            k_initial: used by PDR.

            SMT-LIB format
        """
        smt_input = ""

        for eq in self.equations:
            if eq.contain_reduced:
                smt_input += eq.smtlib_with_order(k, k_initial, self.places_reduced,
                                                  [*self.places_initial] + self.additional_vars) + '\n'

        return smt_input

    def smtlib_link_nets(self, k, k_initial=None):
        """ Assert equalities between places common to the initial and reduced nets.

            k:         used by BMC and PDR,
            k_initial: used by PDR.

            SMT-LIB format
        """
        smt_input = ""

        for pl in self.places_reduced:
            if pl in self.places_initial:
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
                content = re.search(r'generated equations\n(.*)?\n\n',
                                    fp.read().replace('#', '.').replace(',', '.'), re.DOTALL)  # '#' and ',' forbidden in SMT-LIB
                if content:
                    for line in re.split('\n+', content.group())[1:-1]:
                        if line.partition(' |- ')[0] not in ['. O', '. C']:
                            self.equations.append(Equation(re.split(r'\s+', line.partition(' |- ')[2]), self))
            fp.close()
        except FileNotFoundError as e:
            sys.exit(e)


class Equation:
    """
    Equation defined by:
    - left members,
    - right members,
    - an operator,
    - a boolean indicating whether the equation
      involves places from the reduced net.
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
        return ' + '.join(map(str, self.left)) + ' = ' + ' + '.join(map(str, self.right))

    def smtlib(self, k_initial=None, other_vars=None):
        """ Assert the equation.

            k_initial:  used by PDR,
            other_vars: identifiers from equations and initial net.

            SMT-LIB format
        """
        if other_vars is None:
            other_vars = []

        return "(assert ({}".format(self.operator) \
               + self.member_smtlib(self.left, k_initial, other_vars) \
               + self.member_smtlib(self.right, k_initial, other_vars) \
               + "))"

    def minizinc(self):
        """ Assert the equation.
            MiniZinc format
        """
        return "constraint " \
               + self.member_minizinc(self.left) \
               + " {} ".format(self.operator) \
               + self.member_minizinc(self.right) \
               + ";\n"

    def member_smtlib(self, member, k_initial, other_vars):
        """ Helper to assert a member (left or right).

            k_initial:  used by PDR,
            other_vars: identifiers from equations and initial net.

            SMT-LIB format
        """
        smt_input = ""

        for var in member:
            if k_initial is None or var.id not in other_vars:
                smt_input += var.smtlib()
            else:
                smt_input += var.smtlib(k_initial)

        if len(member) > 1:
            smt_input = " (+{})".format(smt_input)

        return smt_input

    def member_minizinc(self, member):
        """ Helper to assert a member (left or right).
            MiniZinc format
        """
        return ' + '.join(map(lambda var: var.minizinc(), member))

    def smtlib_with_order(self, k, k_initial, places_reduced, other_vars=None):
        """ Assert equations with order.

            k:              used by BMC and PDR
            k_initial:      used by PDR
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and initial net
            
            SMTLIB format
        """
        if other_vars is None:
            other_vars = []

        return "(assert ({}".format(self.operator) \
               + self.member_smtlib_with_order(self.left, k, k_initial, places_reduced, other_vars) \
               + self.member_smtlib_with_order(self.right, k, k_initial, places_reduced, other_vars) \
               + "))"

    def member_smtlib_with_order(self, member, k, k_initial, places_reduced=None, other_vars=None):
        """ Helper to assert a member with order (left or right).

            k:              used by BMC and PDR,
            k_initial:      used by PDR,
            places_reduced: place identifiers from the reduced net,
            other_vars:     other identifiers from equations and initial net.
            
            SMTLIB format
        """
        if places_reduced is None:
            places_reduced = []

        if other_vars is None:
            other_vars = []

        smt_input = ""
        for var in member:
            if var.id in places_reduced:
                smt_input += var.smtlib(k)
            elif k_initial is not None and var.id in other_vars:
                smt_input += var.smtlib(k_initial)
            else:
                smt_input += var.smtlib()

        if len(member) > 1:
            smt_input = " (+{})".format(smt_input)

        return smt_input

    def parse_equation(self, eq, system):
        """ Equation parser.
            Input format: .net (output of the `reduced` tool)
        """
        left_parsing, inversed = True, False

        for element in eq:
            if element != '+':
                if element in ['=', '<=', '>=', '<', '>']:
                    self.operator = element
                    left_parsing = False
                else:
                    multiplier = None

                    if '-1.' in element:
                        element = element.replace('-1.', '')  
                        inversed = True
                    
                    elif element.rfind('.') > element.rfind('}'):
                        index = element.rfind('.')
                        element, multiplier = element[:index], element[index+1:] 

                    variable = element.replace('{', '').replace('}','')
                    self.check_variable(variable, system)

                    if left_parsing:
                        self.left.append(Variable(variable, multiplier))
                    else:
                        self.right.append(Variable(variable, multiplier))

        if inversed:
            self.left.append(self.right.pop(0))
            if not self.right:
                self.right.append('0')

    def check_variable(self, element, system):
        """ Check if a given element is an additional variable and a place from the reduced net.
        """
        if not element.isnumeric():
            if element not in system.places_initial and element not in system.additional_vars:
                system.additional_vars.append(element)
            if element in system.places_reduced:
                self.contain_reduced = True


class Variable:
    """
    Variable defined by:
    - an identifier,
    - a multiplier (if there is one).
    """

    def __init__(self, id, multiplier=None):
        """ Initializer.
        """
        self.id = id
        self.multiplier = multiplier

    def __str__(self):
        """ Variable to .net format.
        """
        text = ""
        if self.multiplier is not None:
            text += "{}.".format(self.multiplier)
        return text + self.id

    def smtlib(self, k=None):
        """ Variable and its multiplier if needed.
            SMT-LIB format
        """
        smtlib_input = self.id
        if k is not None:
            smtlib_input += "@{}".format(k)
        if self.multiplier is not None:
            smtlib_input = "(* {} {})".format(self.multiplier, smtlib_input)
        return " {}".format(smtlib_input)

    def minizinc(self):
        """ Variable and its multiplier if needed.
            MiniZinc format
        """
        minizinc_input = self.id
        if self.multiplier:
            minizinc_input = "({} * {})".format(self.multiplier, minizinc_input)
        return minizinc_input


if __name__ == "__main__":

    if len(sys.argv) < 3:
        sys.exit("Argument missing: ./system.py <path_to_initial_Petri_net> <path_to_reduced_Petri_net>")

    ptnet = PetriNet(sys.argv[1])
    ptnet_reduced = PetriNet(sys.argv[2])

    system = System(sys.argv[2], ptnet.places.keys(), ptnet_reduced.places.keys())

    print("> Textual Equations")
    print("-------------------")
    print(system)

    print("> Generated SMT-LIB")
    print("-------------------")
    print(system.smtlib())
