#!/usr/bin/env python3

"""
Properties Parser and Generator

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

import sys
import uuid
import xml.etree.ElementTree as ET

from ptnet import PetriNet


class Properties:
    """
    Properties defined by:
    - an associated Petri net,
    - a set of formulas.
    """

    def __init__(self, ptnet, xml_filename=None):
        """ Initializer.
        """
        self.ptnet = ptnet
        self.formulas = {}

        if xml_filename is not None:
            self.parse_xml(xml_filename)

    def __str__(self):
        """ Properties to textual format.
        """
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "-> Property {}\n{}\n\n".format(formula_id, formula)
        return text

    def smtlib(self):
        """ Assert properties.
            SMT-LIB format
        """
        smt_input = ""
        for formula_id, formula in self.formulas.items():
            smt_input += "; -> Property {}\n{}\n".format(formula_id, formula.smtlib())
        return smt_input

    def parse_xml(self, filename):
        """ Properties parser.
            Input format: .xml
        """
        tree = ET.parse(filename)
        properties_xml = tree.getroot()

        for property_xml in properties_xml:
            property_id = property_xml[0].text
            formula_xml = property_xml[2]
            self.add_formula(Formula(self.ptnet, formula_xml), property_id)

    def add_formula(self, formula, property_id=None):
        """ Add a formula.
            Generate a random property id if necessary.
        """
        if property_id is None:
            property_id = uuid.uuid4()

        self.formulas[property_id] = formula


class Formula:
    """
    Formula defined by:
    - R and P,
    - a property definition.
    """

    def __init__(self, ptnet, formula_xml=None):
        """ Initializer.
        """
        self.ptnet = ptnet

        self.R = None
        self.P = None

        self.property_def = ""
        self.non_monotonic = False

        if formula_xml is not None:
            _, _, node = formula_xml.tag.rpartition('}')
            if node != 'formula':
                raise ValueError("Invalid formula")
            self.parse_xml(formula_xml[0])

    def parse_xml(self, formula_xml, negation=False):
        """ Formula parser.
            Input format: .xml
        """
        _, _, node = formula_xml.tag.rpartition('}')

        if node in ['exists-path', 'all-paths']:
            _, _, child = formula_xml[0].tag.rpartition('}')

            if (node, child) == ('exists-path', 'finally'):
                self.property_def = child
                self.R = self.parse_xml(formula_xml[0][0])
                self.P = StateFormula([self.R], 'not')

            if (node, child) == ('all-paths', 'globally'):
                self.property_def = child
                self.P = self.parse_xml(formula_xml[0][0])
                self.R = StateFormula([self.P], 'not')

        if node == 'deadlock':
            return self.generate_deadlock()

        if node in ['negation', 'conjunction', 'disjunction']:
            negation ^= node == 'negation'
            operands = [self.parse_xml(operand_xml, negation=negation) for operand_xml in formula_xml]
            return StateFormula(operands, node)

        if node == 'is-fireable':
            transitions, clauses = [self.ptnet.transitions[tr.text.replace('#', '')] for tr in formula_xml], []
            for tr in transitions:
                inequalities = []
                for pl, weight in tr.inputs.items():
                    if weight > 0:
                        inequality = Atom(TokenCount([pl]), IntegerConstant(weight), '>=')
                        if (self.property_def == 'finally' and negation) or (self.property_def == 'globally' and not negation):
                            self.non_monotonic = True
                    else:
                        inequality = Atom(TokenCount([pl]), IntegerConstant(-weight), '<')
                        if (self.property_def == 'finally' and not negation) or (self.property_def == 'globally' and negation):
                            self.non_monotonic = True
                    inequalities.append(inequality)
                clauses.append(StateFormula(inequalities, 'and'))
            return StateFormula(clauses, 'or')

        if node == 'integer-le':
            left_operand = self.parse_xml(formula_xml[0], negation=negation)
            right_operand = self.parse_xml(formula_xml[1], negation=negation)

            finally_monotonic = self.property_def == 'finally' \
                                and ((not negation and isinstance(left_operand, IntegerConstant) and isinstance(right_operand, TokenCount)) \
                                    or (negation and isinstance(left_operand, TokenCount) and isinstance(right_operand, IntegerConstant)))
            globally_monotonic = self.property_def == 'globally' \
                                and ((negation and isinstance(left_operand, IntegerConstant) and isinstance(right_operand, TokenCount)) \
                                    or (not negation and isinstance(left_operand, TokenCount) and isinstance(right_operand, IntegerConstant)))

            if not (finally_monotonic or globally_monotonic):
                self.non_monotonic = True

            return Atom(left_operand, right_operand, '<=')

        if node == 'tokens-count':
            places = [self.ptnet.places[place.text.replace('#', '')] for place in formula_xml]
            return TokenCount(places)

        if node == 'integer-constant':
            value = int(formula_xml.text)
            return IntegerConstant(value)

    def __str__(self):
        """ Formula to textual format.
        """
        return "--> R\n{}\n\n--> P\n{}".format(str(self.R), str(self.P))

    def smtlib(self):
        """ Formula.
            SMT-LIB format
        """
        return "; --> R\n{}\n; --> P\n{}".format(self.R.smtlib(assertion=True), self.P.smtlib(assertion=True))

    def generate_deadlock(self):
        """ `deadlock` formula generator.
        """
        clauses_R = []

        for tr in self.ptnet.transitions.values():
            inequalities_R = []

            for pl, weight in tr.inputs.items():
                if weight > 0:
                    ineq_R = Atom(TokenCount([pl]), IntegerConstant(weight), '<')
                else:
                    ineq_R = Atom(TokenCount([pl]), IntegerConstant(-weight), '>=')
                inequalities_R.append(ineq_R)

            clauses_R.append(StateFormula(inequalities_R, 'or'))

        self.R = StateFormula(clauses_R, 'and')
        self.P = StateFormula([self.R], 'not')

        self.property_def = 'finally'
        self.non_monotonic = True

        return self.R

    def generate_quasi_liveness(self, transitions):
        """ `quasi-liveness` formula generator.
        """
        clauses_R = []

        for tr_id in transitions:
            inequalities_R = []

            for pl, weight in self.ptnet.transitions[tr_id].inputs.items():
                if weight > 0:
                    ineq_R = Atom(TokenCount([pl]), IntegerConstant(weight), '>=')
                else:
                    ineq_R = Atom(TokenCount([pl]), IntegerConstant(-weight), '<')
                    self.non_monotonic = True
                inequalities_R.append(ineq_R)

            clauses_R.append(StateFormula(inequalities_R, 'and'))

        self.R = StateFormula(clauses_R, 'or')
        self.P = StateFormula([self.R], 'not')
        self.property_def = 'finally'

    def generate_reachability(self, marking):
        """ `reachability` formula generator.
        """
        clauses_R = []

        for pl, tokens in marking.items():
            clauses_R.append(Atom(TokenCount([pl]), IntegerConstant(tokens), '>='))

        self.R = StateFormula(clauses_R, 'and')
        self.P = StateFormula([self.R], 'not')
        self.property_def = 'finally'

    def result(self, sat):
        """ Display the result.
        """
        if self.property_def == 'finally':
            if sat:
                return "TRUE"
            else:
                return "FALSE"

        if self.property_def == 'globally':
            if sat:
                return "FALSE"
            else:
                return "TRUE"


class StateFormula:
    """
    StateFormula defined by:
    - a list of operands,
    - a boolean operator (and, or, not).
    """

    def __init__(self, operands, operator):
        """ Initializer.
        """
        self.operands = operands

        if operator in ['not', 'and', 'or']:
            self.operator = operator
        elif operator == 'negation':
            self.operator = 'not'
        elif operator == 'conjunction':
            self.operator = 'and'
        elif operator == 'disjunction':
            self.operator = 'or'
        else:
            raise ValueError("Invalid operator for a state formula")

    def __str__(self):
        """ State formula to textual format.
        """
        if self.operator == 'not':
            return "(not {})".format(self.operands[0])

        text = " {} ".format(self.operator).join(map(str, self.operands))

        if len(self.operands) > 1:
            text = "({})".format(text)

        return text

    def smtlib(self, k=None, assertion=False, negation=False):
        """ State formula.
            SMT-LIB format
        """
        smt_input = ''.join(map(lambda operand: operand.smtlib(k), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            smt_input = "({} {})".format(self.operator, smt_input)

        if negation:
            smt_input = "(not {})".format(smt_input)

        if assertion:
            smt_input = "(assert {})\n".format(smt_input)

        return smt_input

    def display_model(self):
        """ Display a model.
        """
        model = ""

        for place_marking in self.operands:
            if place_marking.right_operand.value > 0:
                model += " {}({})".format(place_marking.left_operand, place_marking.right_operand)

        if model == "":
            model = " empty marking"

        print("# Model:", model, sep='')


class Atom:
    """
    Atom defined by:
    - a left operand,
    - a right operand,
    - an operator (=, <=, >=, <, >, distinct).
    """

    def __init__(self, left_operand, right_operand, operator):
        """ Initializer.
        """
        if operator not in ['=', '<=', '>=', '<', '>', 'distinct']:
            raise ValueError("Invalid operator for an atom")

        self.left_operand = left_operand
        self.right_operand = right_operand

        self.operator = operator

    def __str__(self):
        """ Atom to textual format.
        """
        return "({} {} {})".format(self.left_operand, self.operator, self.right_operand)

    def smtlib(self, k=None, assertion=False, negation=False):
        """ Atom.
            SMT-LIB format
        """
        smt_input = "({} {} {})".format(self.operator, self.left_operand.smtlib(k), self.right_operand.smtlib(k))

        if negation:
            smt_input = "(not {})".format(smt_input)

        if assertion:
            smt_input = "(assert {})\n".format(smt_input)

        return smt_input


class TokenCount:
    """
    Token count defined by:
    - a list of places.
    """

    def __init__(self, places):
        """ Initializer
        """
        self.places = places

    def __str__(self):
        """ Token count to textual format.
        """
        smt_input = ' + '.join(map(lambda pl: pl.id, self.places))

        if len(self.places) > 1:
            smt_input = "({})".format(smt_input)

        return smt_input

    def smtlib(self, k=None):
        """ Token count.
            SMT-LIB format
        """
        if k is not None:
            smt_input = ' '.join(map(lambda pl: "{}@{}".format(pl.id, k), self.places))
        else:
            smt_input = ' '.join(map(lambda pl: pl.id, self.places))

        if len(self.places) > 1:
            smt_input = "(+ {})".format(smt_input)

        return smt_input


class IntegerConstant:
    """ 
    Integer constant.
    """

    def __init__(self, value):
        """ Initializer.
        """
        self.value = value

    def __str__(self):
        """ Integer constant to textual format.
        """
        return str(self.value)

    def smtlib(self, k=None):
        """ Integer constant.
            SMT-LIB format
        """
        return str(self.value)


if __name__ == '__main__':

    if len(sys.argv) < 2:
        sys.exit("Argument missing: ./properties.py <path_to_Petri_net> [<path_to_xml_properties>]")

    ptnet = PetriNet(sys.argv[1])

    if len(sys.argv) == 2:
        properties = Properties(ptnet)
        formula = Formula(ptnet)
        formula.generate_deadlock()
        properties.add_formula(formula)
    else:
        properties = Properties(ptnet, sys.argv[2])

    print("> Textual Formula")
    print("-----------------")
    print(properties)

    print("> Generated SMT-LIB")
    print("-------------------")
    print(properties.smtlib())
