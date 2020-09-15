#!/usr/bin/env python3

"""
Formula Generator Module

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
import uuid
import xml.etree.ElementTree as ET

from pn import PetriNet


class Properties:
    """
    Properties parsed from .xml file defined by:
    - an associated Petri Net,
    - a set of Formulas.
    """

    def __init__(self, pn, xml_filename=None):
        """ Initializer.
        """
        self.pn = pn
        self.formulas = {}

        if xml_filename is not None:
            self.parse_xml(xml_filename)

    def __str__(self):
        """ Properties to textual format.
        """
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "--- Property {} ---\n".format(formula_id) + str(formula) + "\n"
        return text

    def smtlib(self):
        """ Assert the properties.

            SMT-LIB format
        """
        smt_input = ""
        for formula_id, formula in self.formulas.items():
            smt_input += "--- Property {} ---\n".format(formula_id) + formula.smtlib() + "\n"
        return smt_input

    def parse_xml(self, filename):
        """ Properties parser.

            Input format: .xml
        """
        tree = ET.parse(filename)
        prop_set = tree.getroot()

        namespace_m = re.match(r'\{.*\}', prop_set.tag)
        if namespace_m:
            namespace = namespace_m.group(0)
        else:
            namespace = ''

        for prop in prop_set:
            formula = None

            property_id = prop.find(namespace + 'id').text
            prop_formula = prop.find(namespace + 'formula')

            deadlock = prop_formula.find(
                './' + namespace + 'exists-path/' + namespace + 'finally/' + namespace + 'deadlock')
            
            fireability = prop_formula.find(
                './' + namespace + 'exists-path/' + namespace + 'finally/' + namespace + 'is-fireable')

            if deadlock is not None:
                self.generate_deadlock(property_id)

            if fireability is not None:
               self.generate_fireability([tr.text for tr in fireability], property_id)
    
    def generate_deadlock(self, property_id=None):
        """ `deadlock` formula generator.
        """
        clauses_R, clauses_P = [], []

        for tr in self.pn.transitions.values():
            inequalities_R, inequalities_P = [], []
            
            for pl, weight in tr.input.items():
                if weight > 0:
                    ineq_R, ineq_P = Inequality(pl, weight, '<'), Inequality(pl, weight, '>=')
                else:
                    ineq_R, ineq_P = Inequality(pl, -weight, '>='), Inequality(pl, -weight, '<')
                
                inequalities_R.append(ineq_R)
                inequalities_P.append(ineq_P)
            
            clauses_R.append(Clause(inequalities_R, 'or'))
            clauses_P.append(Clause(inequalities_P, 'and'))
        
        R, P = Clause(clauses_R, 'and'), Clause(clauses_P, 'or')
        self.add_formula(Formula(R, P, 'deadlock'), property_id)

    def generate_fireability(self, transitions, property_id=None):
        """ `fireability` formula generator.
        """
        clauses_R, clauses_P = [], []

        for tr_id in transitions:
            inequalities_R, inequalities_P = [], []

            for pl, weight in self.pn.transitions[tr_id].input.items():
                if weight > 0:
                    ineq_R, ineq_P = Inequality(pl, weight, '>='), Inequality(pl, weight, '<')
                else:
                    ineq_R, ineq_P = Inequality(pl, -weight, '<'), Inequality(pl, -weight, '>=')
                
                inequalities_R.append(ineq_R)
                inequalities_P.append(ineq_P)

            clauses_R.append(Clause(inequalities_R, "and"))
            clauses_P.append(Clause(inequalities_P, "or"))
        
        R, P = Clause(clauses_R, "or"), Clause(clauses_P, "and")
        self.add_formula(Formula(R, P, "quasi_liveness"), property_id)

    def generate_reachability(self, marking, property_id=None):
        """ `reachability` formula generator.
        """
        clauses_R, clauses_P = [], []

        for pl, tokens in marking.items():
            clauses_R.append(Inequality(pl, tokens, '>='))
            clauses_P.append(Inequality(pl, tokens, '<'))

        R, P = Clause(clauses_R, 'and'), Clause(clauses_P, 'or')
        self.add_formula(Formula(R, P, 'reachability'), property_id)

    def add_formula(self, formula, property_id):
        """ Add formulas.
            Generate a random property id if necessary.
        """
        if property_id is None:
            property_id = uuid.uuid4()

        self.formulas[property_id] = formula

class Formula:
    """
    Formula defined by:
    - two clauses (R and P <=> -R),
    - a property definition.
    """

    def __init__(self, R, P, property_def):
        """ Initializer.
        """
        if property_def not in ['deadlock', 'reachability', 'quasi_liveness']:
            raise ValueError("Invalid property definition")

        self.R = R
        self.P = P

        self.property_def = property_def

    def __str__(self):
        """ Formula to textual format.
        """
        return ">> R\n----\n{}\n\n>> P\n----\n{}".format(str(self.R), str(self.P))

    def smtlib(self):
        """ Formula.

            SMT-LIB format
        """
        return ">> R\n----\n{}\n>> P\n----\n{}".format(self.R.smtlib(assertion=True), self.P.smtlib(assertion=True))

    def result(self, sat):
        """ Display the result.
        """
        if self.property_def == 'deadlock':
            if sat:
                print("Deadlock.")
            else:
                print("Deadlock-free")

        if self.property_def == 'reachability':
            if sat:
                print("Reachable.")
            else:
                print("Unreachable.")

        if self.property_def == 'quasi_liveness':
            if sat:
                print("Fireable.")
            else:
                print("Unfireable.")


class Clause:
    """
    Clause defined by:
    - a set of operands,
    - a boolean operator.
    """

    def __init__(self, operands, operator):
        """ Initializer.
        """
        if operator not in ['and', 'or']:
            raise ValueError("Invalid operator for a clause")

        self.operands = operands
        self.operator = operator

    def __str__(self):
        """ Clause to textual format.
        """
        text = " {} ".format(self.operator).join(map(str, self.operands))

        if len(self.operands) > 1:
            text = "({})".format(text)

        return text

    def smtlib(self, k=None, assertion=False, negation=False):
        """ Clause.

            SMT-LIB format
        """
        smt_input = ''.join(map(lambda operand: operand.smtlib(k), self.operands))
        
        if len(self.operands) > 1:
            smt_input = "({} {})".format(self.operator, smt_input)
        
        if negation:
            smt_input = "(not {})".format(smt_input)
        
        if assertion:
            smt_input = "(assert {})\n".format(smt_input)
        
        return smt_input


class Inequality:
    """
    Inequality defined by:
    - a left operand,
    - a right operand,
    - an operator (=, <=, >=, <, >, distinct).
    """

    def __init__(self, left_operand, right_operand, operator):
        """ Initializer.
        """
        if operator not in ['=', '<=', '>=', '<', '>', 'distinct']:
            raise ValueError("Invalid operator for an inequality")

        self.left_operand = left_operand
        self.right_operand = right_operand

        self.operator = operator

    def __str__(self):
        """ Inequality to textual format.
        """
        return "({} {} {})".format(self.left_operand.id, self.operator, self.right_operand)

    def smtlib(self, k=None):
        """ Inequality.

            SMT-LIB format
        """
        if k is not None:
            return "({} {}@{} {})".format(self.operator, self.left_operand.id, k, self.right_operand)
        else:
            return "({} {} {})".format(self.operator, self.left_operand.id, self.right_operand)


if __name__ == '__main__':

    if len(sys.argv) == 1:
        exit("File missing: ./properties.py <path_to_Petri_net> <path_to_xml_properties>")

    pn = PetriNet(sys.argv[1])
    properties = Properties(pn, sys.argv[2])

    print("> Textual Formula")
    print("-----------------")
    print(properties)

    print("> Generated SMTlib2")
    print("-------------------")
    print(properties.smtlib())
