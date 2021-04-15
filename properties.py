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
__version__ = "3.0.0"

import itertools
import operator
import sys
import uuid
import xml.etree.ElementTree as ET
from abc import ABC, abstractmethod

from ptnet import PetriNet

COMPARISON_OPERATORS = {
    '=': operator.eq,
    '<=': operator.le,
    '>=': operator.ge,
    '<': operator.lt,
    '>': operator.gt,
    'distinct': operator.ne
}

NEGATION_COMPARISON_OPERATORS = {
    '=': 'distinct',
    '<=': '>',
    '>=': '<',
    '<': '>=',
    '>': '<=',
    'distinct': '='
}

COMMUTATION_COMPARISON_OPERATORS = {
    '=': '=',
    '<=': '>=',
    '>=': '<=',
    '<': '>',
    '>': '<',
    'distinct': 'distinct'
}

PNML_BOOLEAN_OPERATORS = {
    'negation': 'not',
    'conjunction': 'and',
    'disjunction': 'or'
}

NEGATION_BOOLEAN_OPERATORS = {
    'and': 'or',
    'or': 'and'
}

MINIZINC_BOOLEAN_OPERATORS = {
    'and': '/\\',
    'or': '\\/'
}


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
            (debugging function)
        """
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "-> Property {}\n{}\n\n".format(formula_id, formula)
        return text

    def smtlib(self):
        """ Assert properties.
            (debugging function)
            SMT-LIB format
        """
        smt_input = ""
        for formula_id, formula in self.formulas.items():
            smt_input += "; -> Property {}\n{}\n".format(formula_id, formula.smtlib())
        return smt_input

    def minizinc(self):
        """ Assert properties.
            (debugging function)
            MiniZinc format
        """
        minizinc_input = ""
        for formula_id, formula in self.formulas.items():
            minizinc_input += "; -> Property {}\n{}\n".format(formula_id, formula.minizinc())
        return minizinc_input

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
            Generate a random property id if not provided.
        """
        if property_id is None:
            property_id = uuid.uuid4()

        self.formulas[property_id] = formula

    def dnf(self):
        """ Convert to Disjunctive Normal Form.
        """
        for formula_id in self.formulas:
            self.formulas[formula_id] = self.formulas[formula_id].dnf()
        return self

class Formula:
    """
    Formula defined by:
    - R: feared events,
    - P: invariant property,
    - a property definition (exists-paths finally, all-paths globally),
    - a monotonicity flag.
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
            clauses = []

            if self.ptnet.colored:
                # colored `.pnml` input Petri net
                transitions = []
                for colored_transition in formula_xml:
                    transitions += [self.ptnet.transitions[tr] for tr in self.petnet.transitions_mapping[colored_transition.text.replace('#', '.')]]

            if self.ptnet.pnml_mappping:
                # `.pnml` input Petri net
                transitions = [self.ptnet.transitions[self.ptnet.transitions_mapping[tr.text.replace('#', '.')]] for tr in formula_xml]

            else:
                # `.net` input Petri net
                transitions = [self.ptnet.transitions[tr.text.replace('#', '.')] for tr in formula_xml]

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
            if self.ptnet.colored:
                # colored `.pnml` input Petri net
                places = []
                for colored_place in formula_xml:
                    places += [self.ptnet.places[pl] for pl in self.ptnet.places_mapping[colored_place.text.replace('#', '.')]]

            elif self.ptnet.pnml_mapping:
                # `.pnml` input Petri net
                places = [self.ptnet.places[self.ptnet.places_mapping[place.text.replace('#', '.')]] for place in formula_xml]

            else:
                # `.net` input Petri net
                places = [self.ptnet.places[place.text.replace('#', '.')] for place in formula_xml]
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
            (debugging function)
            SMT-LIB format
        """
        return "; --> R\n{}\n; --> P\n{}".format(self.R.smtlib(assertion=True), self.P.smtlib(assertion=True))

    def minizinc(self):
        """ Formula.
            (debugging function)
            MiniZinc format
        """
        return "; --> R\n{}\n; --> P\n{}".format(self.R.minizinc(assertion=True), self.P.minizinc(assertion=True))

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

            if len(inequalities_R) > 1:
                clauses_R.append(StateFormula(inequalities_R, 'or'))
            else:
                clauses_R.append(inequalities_R[0])

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

    def result(self, reachable):
        """ Display the result according to the reachability of the feared events R.
        """
        if self.property_def == 'finally':
            if reachable:
                return "TRUE"
            else:
                return "FALSE"

        if self.property_def == 'globally':
            if reachable:
                return "FALSE"
            else:
                return "TRUE"

    def dnf(self):
        """ Convert to Disjunctive Normal Form.
        """
        formula = Formula(self.ptnet)
        formula.non_monotonic, formula.property_def = self.non_monotonic, self.property_def
        formula.P, formula.R = self.P.dnf(), self.R.dnf()
        return formula


class Expression(ABC):
    """ TODO
    """


class StateFormula(Expression):
    """
    StateFormula defined by:
    - a list of operands,
    - a boolean operator (not, and, or).
    """

    def __init__(self, operands, operator):
        """ Initializer.
        """
        self.operands = operands

        if operator in ['not', 'and', 'or']:
            self.operator = operator
        elif operator in ['negation', 'conjunction', 'disjunction']:
            self.operator = PNML_BOOLEAN_OPERATORS[operator]
        else:
            raise ValueError("Invalid operator for a state formula")

    def __str__(self):
        """ State formula to textual format.
            (debugging function)
        """
        if self.operator == 'not':
            return "(not {})".format(self.operands[0])

        text = " {} ".format(self.operator).join(map(str, self.operands))

        if len(self.operands) > 1:
            text = "({})".format(text)

        return text

    def __eq__(self, other):
        """ Compare StateFormulas for equality.
        """
        if not isinstance(other, StateFormula):
            return NotImplemented
        else:
            return self.operands == other.operands and self.operator == other.operator

    def __hash__(self):
        """ Hash StateFormula.
        """
        return hash((tuple(self.operands), self.operator))

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

    def minizinc(self, assertion=False):
        """ State formula.
            MiniZinc format
        """
        if len(self.operands) > 1:
            operator = MINIZINC_BOOLEAN_OPERATORS[self.operator]
        else:
            operator = ''

        minizinc_input = ' {} '.format(operator).join(map(lambda operand: operand.minizinc(), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            minizinc_input = "({})".format(minizinc_input)

        if self.operator == 'not':
            minizinc_input = "(not {})".format(minizinc_input)

        if assertion:
            minizinc_input = "constraint {};\n".format(minizinc_input)

        return minizinc_input

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

    def negation(self):
        """ Return the negation of the StateFormula.
        """
        return StateFormula([operand.negation() for operand in self.operands], NEGATION_BOOLEAN_OPERATORS[self.operator])

    def dnf(self, negation_propagation=False):
        """ Convert to Disjunctive Normal Form.
        """
        if self.operator == 'not':
            if negation_propagation:
                # DNF(not (not P)) <-> DNF(P)
                return self.operands[0].dnf()
            else:
                # DNF(not P)
                return self.operands[0].dnf(negation_propagation=True)

        elif self.operator == 'and':
            if negation_propagation:
                # DNF(not (P and Q)) <-> DNF((not P) or (not Q))
                return StateFormula([operand.dnf(negation_propagation) for operand in self.operands], 'or').dnf()
            else:
                # DNF(P and Q) <-> (P1 and Q1) or ... or (Pm and Q1) or ... or (Pm and Qn)
                # with (DNF P) = (P1 or ... or Pm) and (DNF Q) = (Q1 or ... or Qn)
                operands = []
                for operand in self.operands:
                    operand_dnf = operand.dnf()
                    if isinstance(operand_dnf, StateFormula):
                        operands.append(operand_dnf.operands)
                    else:
                        operands.append([operand_dnf])

                clauses = []
                for combination in itertools.product(*operands):
                    combination_factorized = []
                    for cube in combination:
                        if isinstance(cube, StateFormula) and cube.operator ==  'and':
                            combination_factorized += cube.operands
                        else:
                            combination_factorized.append(cube)
                    clauses.append(StateFormula(combination_factorized, 'and'))

            return StateFormula(clauses, 'or')
        
        elif self.operator == 'or':
            if negation_propagation:
                # DNF(not (P or Q)) <-> DNF((not P) and (not Q))
                return StateFormula([operand.dnf(negation_propagation) for operand in self.operands], 'and').dnf()
            else:
                # DNF(P and Q) <-> DNF(P) and DNF(Q)
                operands_dnf = []
                
                for operand in self.operands:
                    operand_dnf = operand.dnf()
                    if isinstance(operand_dnf, StateFormula):
                        operands_dnf += operand_dnf.operands
                    else:
                        operands_dnf.append(operand_dnf)
                return StateFormula(operands_dnf, 'or')

        else:
            raise ValueError("Invalid operator for a state formula")

    def reached_cube(self, m):
        """ Return a cube satisfied by marking m.
            Assume the formula is in DNF and satisfied by m.
        """
        if self.operator == 'or':
            for cube in self.operands:
                if cube.eval(m):
                    return cube
        else:
            return self

    def eval(self, m):
        """ Evaluate the StateFomula with marking m.
        """
        if self.operator == 'not':
            return not self.operands[0].eval(m)
        
        elif self.operator == 'and':
            return all(operand.eval(m) for operand in self.operands)
        
        elif self.operator == 'or':
            return any(operand.eval(m) for operand in self.operands)
        
        else:
            return False

    def generalization(self, tr):
        """ Generalize a state leading to feared states.
        """
        generalized_operands = [operand.generalization(tr, firing_condition=False) for operand in self.operands]

        for place, weight in tr.pre.items():
            generalized_operands.append(Atom(TokenCount([place]), IntegerConstant(weight), '>='))    

        return StateFormula(generalized_operands, 'and')


class Atom(Expression):
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
            (debugging function)
        """
        return "({} {} {})".format(self.left_operand, self.operator, self.right_operand)

    def __eq__(self, other):
        """ Compare Atoms for equality.
        """
        if not isinstance(other, Atom):
            return NotImplemented
        else:
            return self.left_operand == other.left_operand and self.right_operand == other.right_operand and self.operator == other.operator

    def __hash__(self):
        """ Hash Atom.
        """
        return hash((self.left_operand, self.operator, self.right_operand))

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

    def minizinc(self, assertion=False):
        """ Atom.
            MiniZinc format
        """
        minizinc_input = "({} {} {})".format(self.left_operand.minizinc(), self.operator, self.right_operand.minizinc())

        if assertion:
            minizinc_input = "constraint {};\n".format(minizinc_input)

        return minizinc_input

    def negation(self):
        """ Return the negation of the Atom.
        """
        return Atom(self.left_operand, self.right_operand, NEGATION_COMPARISON_OPERATORS[self.operator])

    def dnf(self, negation_propagation=False):
        """ Convert to Disjunctive Normal Form.
        """
        if negation_propagation:
            # DNF(not (P comp Q)) <-> P (not comp) Q
            return Atom(self.left_operand, self.right_operand, NEGATION_COMPARISON_OPERATORS[self.operator]).dnf()
        else:
            # DNF(P comp Q) <-> P comp Q 
            if isinstance(self.left_operand, IntegerConstant) and isinstance(self.right_operand, TokenCount):
                # Normalization: TokenCount at left and IntegerConstant at right
                return Atom(self.right_operand, self.left_operand, COMMUTATION_COMPARISON_OPERATORS[self.operator])
            else:
                return self

    def reached_cube(self, m):
        """ Return a cube satisfied by marking m.
            Assume the formula is in DNF and satisfied by m.
        """
        return self

    def eval(self, m):
        """ Evaluate the subformula with marking m.
        """
        return COMPARISON_OPERATORS[self.operator](self.left_operand.eval(m), self.right_operand.eval(m))

    def generalization(self, tr, firing_condition=True):
        """ Generalize a state leading to feared states.
        """
        left_operand = self.left_operand.generalization(tr)
        right_operand = self.right_operand.generalization(tr)

        # Normalization: value at right
        right_operand.value -= left_operand.value
        left_operand.value = 0

        if firing_condition:
            atoms = [Atom(left_operand, right_operand, self.operator)]
            for place, weight in tr.pre.items():
                atoms.append(Atom(TokenCount([place]), IntegerConstant(weight), '>='))
            return StateFormula(atoms, 'and')
        else:
            return Atom(left_operand, right_operand, self.operator)


class TokenCount(Expression):
    """
    Token count defined by:
    - a list of places.
    """

    def __init__(self, places, value=0):
        """ Initializer
        """
        self.places = places
        self.value = value

    def __str__(self):
        """ Token count to textual format.
            (debugging function)
        """
        smt_input = ' + '.join(map(lambda pl: pl.id, self.places))

        if self.value:
            smt_input += " {} {}".format(self.sign(), abs(self.value))

        if len(self.places) > 1:
            smt_input = "({})".format(smt_input)

        return smt_input

    def __eq__(self, other):
        """ Compare TokenCounts for equality.
        """
        if not isinstance(other, TokenCount):
            return NotImplemented
        else:
            return self.places == other.places and self.value == other.value

    def __hash__(self):
        """ Hash TokenCount.
        """
        return hash((tuple(self.places), self.value))

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

        if self.value:
            smt_input = "({} {} {})".format(self.sign(), smt_input, abs(self.value))

        return smt_input

    def minizinc(self):
        """ Token count.
            MiniZinc format
        """
        minizinc_input = ' + '.join(map(lambda pl: pl.id, self.places))

        if len(self.places) > 1:
            minizinc_input = "({})".format(minizinc_input)

        if self.value:
            minizinc_input = "({} {} {})".format(minizinc_input, self.sign(), self.value)

        return minizinc_input

    def dnf(self, negation_propagation=False):
        """ Convert to Disjunctive Normal Form.
        """
        # Normalization: lexicographic order
        self.places = sorted(self.places, key=lambda pl: pl.id)

        # DNF(P1 + ... + Pn) = P1 + ... + Pn
        return self

    def sign(self):
        """ Return the sign of the value.
        """
        if self.value < 0:
            return '-'
        else:
            return '+'

    def eval(self, m):
        """ Evaluate the subformula with marking m.
        """
        return sum([m[pl] for pl in self.places]) + self.value

    def generalization(self, tr):
        """ Generalize a state leading to feared states.
        """
        pre = sum([tr.inputs[place] for place in self.places if place in tr.inputs])
        post = sum([tr.outputs[place] for place in self.places if place in tr.outputs])
        
        delta = post - pre
        
        return TokenCount(self.places, self.value + delta)

class IntegerConstant(Expression):
    """ 
    Integer constant.
    """

    def __init__(self, value):
        """ Initializer.
        """
        self.value = value

    def __str__(self):
        """ Integer constant to textual format.
            (debugging function)
        """
        return str(self.value)

    def __eq__(self, other):
        """ Compare IntegerConstants for equality.
        """
        if not isinstance(other, IntegerConstant):
            return NotImplemented
        else:
            return self.value == other.value

    def __hash__(self):
        """ Hash IntegerConstant.
        """
        return hash(self.value)

    def smtlib(self, k=None):
        """ Integer constant.
            SMT-LIB format
        """
        return str(self)

    def minizinc(self):
        """ Integer constant.
            MiniZinc format
        """
        return str(self)

    def dnf(self, negation_propagation=False):
        """ Convert to Disjunctive Normal Form.
        """
        # DNF(k) = k
        return self

    def eval(self, m):
        """ Evaluate the subformula with marking m.
        """
        return self.value

    def generalization(self, tr):
        """ Generalize a state leading to feared states.
        """
        return IntegerConstant(self.value)


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

    print("> Disjunctive Normal Form")
    print("-------------------------")
    print(properties.dnf())
