#!/usr/bin/env python3

"""
Reduction Equations Module

Equations provided by the tool `reduce`
Input file format: .net
"""

import re
import sys


class System:
    """
    Equation system defined by:
    - a set of places from the original Petri Net
    - a set of places from the reduced Petri Net
    - a set of additional variables
    - a set of (in)equations
    """
    def __init__(self, filename, places = [], places_reduced = []):
        self.places = places
        self.places_reduced = places_reduced
        self.additional_vars = []

        self.system = []

        self.parser(filename)

    def __str__(self):
        """ Equations to `reduce` tool format
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

    def smtlib_only_non_reduced_places(self, k_original=None):
        """ Equations not involving places in the reduced net,
            Declarations of the additional variables,
            k_original: used by IC3.
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            if var not in self.places_reduced:
                var_name = var if k_original is None else "{}@{}".format(var, k_original) 
                smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var_name, var_name)
        for eq in self.system:
            if not eq.contain_reduced:
                smt_input += eq.smtlib(k_original, [*self.places] + self.additional_vars) + '\n'
        return smt_input
        
    def smtlib_ordered(self, k, k_original=None):
        """ Equations involving places in the reduced net,
            k:          used by k-induction and IC3,
            k_original: used by IC3.
            SMR-LIB format
        """
        smt_input = ""
        for eq in self.system:
            if eq.contain_reduced:
                smt_input += eq.smtlib_ordered(k, k_original, self.places_reduced, [*self.places] + self.additional_vars) + '\n'
        for pl in self.places_reduced:
            if pl in self.places:
                if k_original is None:
                    smt_input += "(assert (= {}@{} {}))\n".format(pl, k, pl)
                else:
                    smt_input += "(assert (= {}@{} {}@{}))\n".format(pl, k, pl, k_original)
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
    - Left member
    - Right member
    - Operator
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

    def smtlib(self, k_original=None, other_vars=[]):
        """ Equation.
            SMT-LIB format
        """
        return "(assert ({}".format(self.operator)                      \
               + self.member_smtlib(self.left, k_original, other_vars)  \
               + self.member_smtlib(self.right, k_original, other_vars) \
               + "))"

    def member_smtlib(self, member, k_original, other_vars):
        """ Member.
            SMT-LIB format
        """
        smt_input = ""
        if len(member) > 1:
            smt_input += " (+"
        for elem in member:
            if k_original is None or elem not in other_vars:
                smt_input += " {}".format(elem)
            else:
                smt_input += " {}@{}".format(elem, k_original)
        if len(member) > 1:
            smt_input += ")"
        return smt_input

    def smtlib_ordered(self, k, k_original, places_reduced, other_vars=[]):
        """ Equation with orders.
            k:              used by k-induction and IC3
            k_original:     used by IC3
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and original net
            SMTLIB format
        """
        return "(assert ({}".format(self.operator)                                                 \
               + self.member_smtlib_ordered(self.left, k, k_original, places_reduced, other_vars)  \
               + self.member_smtlib_ordered(self.right, k, k_original, places_reduced, other_vars) \
               + "))"

    def member_smtlib_ordered(self, member, k, k_original, places_reduced=[], other_vars = []):
        """ Equation with orders.
            k:              used by k-induction and IC3
            k_original:     used by IC3
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and original net
            SMTLIB format
        """
        smt_input = ""
        if len(member) > 1:
            smt_input += " (+"
        for elem in member:
            if elem in places_reduced:
                smt_input += " {}@{}".format(elem, k)
            elif k_original is not None and elem in other_vars:
                smt_input += " {}@{}".format(elem, k_original)
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


if __name__ == "__main__":
    
    if len(sys.argv) == 1:
        exit("File missing: ./eq <path_to_file>")
    
    system = System(sys.argv[1])
    
    print("Equations")
    print("---------")
    print(system)
    
    print("\nSMTlib2 Format")
    print("--------------")
    print(system.smtlib())
