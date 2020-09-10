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
    - a set of places from the initial Petri Net,
    - a set of places from the reduced Petri Net,
    - a set of additional variables,
    - a set of (in)equations.
    """

    def __init__(self, filename, places=[], places_reduced=[]):
        self.places = places
        self.places_reduced = places_reduced
        self.additional_vars = []

        self.system = []

        self.parser(filename)

    def __str__(self):
        """ Equations to `reduce` tool format.
        """
        text = ""
        for eq in self.system:
            text += str(eq) + '\n'
        return text

    def smtlib(self):
        """ Equations,
            Declarations of the additional variables.
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var)
        for eq in self.system:
            smt_input += eq.smtlib() + '\n'
        return smt_input

    def smtlib_only_non_reduced_places(self, k_initial=None):
        """ Equations not involving places in the reduced net,
            Declarations of the additional variables,
            k_initial: used by IC3.
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            if var not in self.places_reduced:
                var_name = var if k_initial is None else "{}@{}".format(var, k_initial)
                smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var_name, var_name)
        for eq in self.system:
            if not eq.contain_reduced:
                smt_input += eq.smtlib(k_initial, [*self.places] + self.additional_vars) + '\n'
        return smt_input

    def smtlib_ordered(self, k, k_initial=None):
        """ Equations involving places in the reduced net,
            k:          used by BMC and IC3,
            k_initial: used by IC3.
            SMR-LIB format
        """
        smt_input = ""
        for eq in self.system:
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
                        self.system.append(Equation(eq, self))
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
        left = True
        for element in eq:
            if element != '+':
                if element in ['=', '<=', '>=', '<', '>']:
                    self.operator = element
                    left = False
                else:
                    element = element.replace('{', '').replace('}', '').replace('#', '')
                    if not element.isnumeric():
                        if element not in system.places and element not in system.additional_vars:
                            system.additional_vars.append(element)
                        if element in system.places_reduced:
                            self.contain_reduced = True
                    if left:
                        self.left.append(element)
                    else:
                        self.right.append(element)


class Relation:
    """
    Graph relation between a net and its reduced net.
    
    A relation is composed of:
    - Agglomerations of Variables,
    - Constant Variables,
    - Equalities between Variables.

    Used for the Concurrent Places Problem.
    See: `concurrent_places.py`
    """

    def __init__(self, eq):
        self.eq = eq

        self.variables = {}

        self.agglomerations = []
        self.constant_vars = []
        self.equal_vars = []

        self.construct()
        self.propagate()

    def __str__(self):
        """ Relation to String:
            - Agglomerations,
            - Constant Variables,
            - Equal Variables.
        """
        text = "Agglomerations\n--------------\n"
        for agglo in self.agglomerations:
            text += str(agglo) + '\n'

        text += "\nConstant Variables\n------------------\n"
        for pl in self.constant_vars:
            text += pl.id + ' = ' + str(pl.value) + '\n'

        text += "\nEqual Variables\n---------------\n"
        for eq in self.equal_vars:
            text += eq[0].id + ' = ' + eq[1].id + '\n'

        return text

    def construct(self):
        """ Parse the equations and construct the relation.
        """
        for eq in self.eq.system:

            left = self.get_variable(eq.left[0])

            if len(eq.right) == 1:

                if eq.right[0].isnumeric():
                    # case p = k or a = k
                    left.value = int(eq.right[0])
                    self.constant_vars.append(left)

                else:
                    # case p = q
                    right = self.get_variable(eq.right[0])
                    left.equals.append(right)
                    right.equals.append(left)
                    self.equal_vars.append([left, right])

            else:
                # case a = p + a' or a = p + q or p = q + r
                left.children.append(self.get_variable(eq.right[0]))
                left.children.append(self.get_variable(eq.right[1]))
                self.agglomerations.append(left)

    def propagate(self):
        """ Propagate places to the head of each agglomeration.
            Propagate value of each agglomeration.
        """
        for var in self.variables.values():
            var.propagate(var.value)

    def get_variable(self, id_var):
        """ Create the corresponding Variable
            if it is not already created,
            otherwise return the corresponding Variable.
        """
        if id_var in self.variables:
            return self.variables[id_var]

        else:
            new_var = Variable(id_var, id_var not in self.eq.places)
            self.variables[id_var] = new_var
            return new_var

    def trivial_c_stables(self):
        """ Return a set of c-stables obtained trivially
            from the reduction equations.
        """
        c_stables = []

        for var in self.agglomerations:
            # a_n = k > 1
            # a_n = p_n + a_n-1
            # ...
            # a_1 = p_1 + p_0
            if var.value > 1:
                c_stable = []
                for pl in var.propagated_places:
                    c_stable.append(pl.id)
                c_stables.append(c_stable)

            # p = q + r
            if not var.additional:
                c_stables.append([var.id, var.children[0].id])
                c_stables.append([var.id, var.children[1].id])

        # constant places and agglomerations (assumption: No dead place)
        for var in self.constant_vars:
            for pl1 in var.propagated_places:
                for pl2 in self.eq.places:
                    if pl2 not in var.propagated_places:
                        c_stables.append([pl1.id, pl2])

        # equals variables
        for (var1, var2) in self.equal_vars:
            if not (var1.additional or var2.additional):
                c_stables.append([var1.id, var2.id])

            else:
                for pl1 in var1.propagated_places:
                    for pl2 in var2.propagated_places:
                        c_stables.append([pl1.id, pl2.id])

        return c_stables

    def c_stable_matrix(self, var1_id, var2_id):
        """ Given two concurrent places from the reduced net
            return associated c-stables in the initial net.
        """
        var1 = self.get_variable(var1_id)
        var2 = self.get_variable(var2_id)

        c_stables = []

        for pl1 in var1.propagated_places:
            for pl2 in var2.propagated_places:
                c_stables.append([pl1.id, pl2.id])

        return c_stables

    def equalities(self):
        """ Return the list of equals places.
            Not used for the moment.
        """
        equals = []
        for var1, var2 in self.equal_vars:
            if not (var1.additional or var2.additional):
                equals.append([var1.id, var2.id])
        return equals


class Variable:
    """
    Place or additional variable.
    Used by the Concurrency Matrix Constructor.
    A variable defined by:
    - an ID,
    - a value,
    - a list of equals variables,
    - a list of children,
    - after propagation, a set of places associated.

    Used for the Concurrent Places Problem.
    See: `concurrent_places.py`
    """

    def __init__(self, id, additional):
        self.id = id
        self.additional = additional

        self.value = -1
        self.equals = []
        self.children = []

        self.propagated_places = set()

        if not self.additional:
            self.propagated_places.add(self)

    def __str__(self):
        text = self.id + ':'
        for var in self.propagated_places:
            text += ' ' + var.id
        return text

    def propagate(self, value):
        """ Recursive propagation for agglomerations.
        """
        # Update value
        if self.value < value:
            self.value = value

        # For each child, propagate it and add the places (recursively)
        for child in self.children:
            if not child.propagated_places:
                child.propagate(value)
            self.propagated_places = self.propagated_places.union(child.propagated_places)

        # For each equal var, propagate it and add the places (recursively)
        for equal in self.equals:
            if not equal.propagated_places:
                equal.propagate(value)
            self.propagated_places = self.propagated_places.union(equal.propagated_places)


if __name__ == "__main__":

    if len(sys.argv) < 3:
        exit("File missing: ./eq <path_to_initial_net> <path_to_reduced_net>")

    pn = PetriNet(sys.argv[1])
    pn_reduced = PetriNet(sys.argv[2])

    eq = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())

    relation = Relation(eq)

    print("Equations")
    print("---------")
    print(eq)

    print("\nSMTlib2 Format")
    print("--------------")
    print(eq.smtlib())

    print("\nRelations")
    print("---------")
    print(relation)
