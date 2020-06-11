#!/usr/bin/env python3

"""
Formula Generator Module
"""

from pn import PetriNet

import re
import sys
import xml.etree.ElementTree as ET


class Properties:
    """
    Properties parsed from .xml file defined by:
    - an associated Petri Net
    - a set of Formulas
    """

    def __init__(self, pn, xml_filename):
        """ Initializer.
        """
        self.pn = pn
        self.formulas = {}
        self.parse_xml(xml_filename)

    def __str__(self):
        """ Properties to logic format.
        """
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "--- Property {} ---\n".format(formula_id)
            text += str(formula)
        return text

    def smtlib(self):
        """ Assertions corresponding to the properties.
            SMT-LIB format
        """
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "; {}\n".format(formula_id)
            text += formula.smtlib()
        return text

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

            prop_id = prop.find(namespace + 'id').text
            prop_formula = prop.find(namespace + 'formula')

            deadlock = prop_formula.find(
                './' + namespace + 'exists-path/' + namespace + 'finally/' + namespace + 'deadlock')
            fireability = prop_formula.find(
                './' + namespace + 'exists-path/' + namespace + 'finally/' + namespace + 'is-fireable')

            if deadlock is not None:
                formula = Formula(self.pn, 'deadlock')

            if fireability is not None:
                transitions = []
                for tr in fireability:
                    transitions.append(tr.text)
                formula = Formula(self.pn, 'fireability', transitions)

            if formula is not None:
                self.formulas[prop_id] = formula


class Formula:
    """
    Formula defined by:
    - an associated Petri Net
    - a set of clauses
    - an operator ('or', 'and') applied between the clauses
    - a property ('deadlock', 'fireability', 'reachability', 'concurrent places')
    """

    def __init__(self, pn, prop='deadlock', transitions=[], marking=[]):
        self.pn = pn
        self.clauses = []
        self.operator = ""
        self.prop = prop

        if prop == 'deadlock':
            self.generate_deadlock()

        if prop == 'fireability':
            self.generate_fireability(transitions)

        if prop == 'reachability':
            self.generate_reachability(marking)

        if prop == 'concurrent_places':
            self.generate_concurrent_places()

    def __str__(self):
        """ Formula to logic format.
        """
        text = ""
        for index, clause in enumerate(self.clauses):
            text += "(" + str(clause) + ")"
            if index != len(self.clauses) - 1:
                text += " and "
        text += "\n"
        return text

    def smtlib(self, k=None):
        """ Assertions corresponding to the formula.
            SMT-LIB format
        """
        if self.operator == "or":
            return self.disjunctive_smtlib(k)
        else:
            return self.conjunctive_smtlib(k)

    def conjunctive_smtlib(self, k=None):
        """ Assertion for a CNF (Conjunctive Normal Form).
            SMT-LIB format
        """
        text = ""
        for clause in self.clauses:
            text += "(assert {})\n".format(clause.smtlib(k))
        return text

    def disjunctive_smtlib(self, k=None):
        """ Assertions for a DNF (Disjunctive Normal Form).
            SMT-LIB format
        """
        text = "(assert (or "
        for clause in self.clauses:
            text += clause.smtlib(k)
        text += "))\n"
        return text

    def generate_deadlock(self):
        """ `deadlock` formula generator.
        """
        for tr in self.pn.transitions.values():
            inequalities = []
            for pl, weight in tr.input.items():
                if weight > 0:
                    ineq = Inequality(pl, weight, '<')
                else:
                    ineq = Inequality(pl, - weight, '>=')
                inequalities.append(ineq)
            self.clauses.append(Clause(inequalities, "or"))
        self.operator = "and"

    def generate_fireability(self, transitions):
        """ `fireability` formula generator.
        """
        for tr_id in transitions:
            inequalities = []
            tr = self.pn.transitions[tr_id]
            for pl, weight in tr.input.items():
                if weight > 0:
                    ineq = Inequality(pl, weight, '>=')
                else:
                    ineq = Inequality(pl, - weight, '<')
                inequalities.append(ineq)
            self.clauses.append(Clause(inequalities, "and"))
        self.operator = "or"

    def generate_reachability(self, marking):
        """ `reachability` formula generator.
        """
        for pl, counter in marking.items():
            self.clauses.append(Inequality(pl, counter, '>='))

    def generate_concurrent_places(self):
        """ `concurrent places` formula generator.
        """
        inequalities = []
        for pl in self.pn.places.values():
            inequalities.append(Inequality(pl, 0, '>'))
        self.clauses.append(Clause([AtLeast(2, inequalities)], 'and'))
        self.operator = "and"

    def result(self, sat):
        """ Display the result.
        """
        if self.prop == "deadlock":
            if sat:
                print("Deadlock.")
            else:
                print("Deadlock free")

        if self.prop == 'reachability':
            if sat:
                print("Reachable.")
            else:
                print("Unreachable.")

        if self.prop == "fireability":
            if sat:
                print("Fireable.")
            else:
                print("Not fireable.")


class Clause:
    """
    Clause defined by:
    - a set of inequalities
    - a boolean operator
    """

    def __init__(self, inequalities, operator):
        if operator not in ["and", "or"]:
            raise ValueError("Invalid operator for a clause")

        self.inequalities = inequalities
        self.operator = operator

    def __str__(self):
        """ Clause to logic format.
        """
        text = ""
        for index, ineq in enumerate(self.inequalities):
            text += str(ineq)
            if index != len(self.inequalities) - 1:
                text += " " + self.operator + " "
        return text

    def smtlib(self, k=None, write_assert=False, neg=False):
        """ Clause.
            SMT-LIB format
        """
        text = ""
        for ineq in self.inequalities:
            text += ineq.smtlib(k)
        if len(self.inequalities) > 1:
            text = "({} {})".format(self.operator, text)
        if neg:
            text = "(not {})".format(text)
        if write_assert:
            text = "(assert {})\n".format(text)
        return text


class Inequality:
    """
    Inequality defined by:
    - a left member
    - a right member
    - an operator (=, <=, >=, <, >, distinct)
    """

    def __init__(self, left_member, right_member, operator):
        if operator not in ["=", "<=", ">=", "<", ">", "distinct"]:
            raise ValueError("Invalid operator for an inequality")

        self.left_member = left_member
        self.right_member = right_member
        self.operator = operator

    def __str__(self):
        """ Inequality to logic format.
        """
        return "{} {} {}".format(self.left_member.id, self.operator, self.right_member)

    def smtlib(self, k=None):
        """ Inequality.
            SMT-LIB format
        """
        if k is not None:
            return "({} {}@{} {})".format(self.operator, self.left_member.id, k, self.right_member)
        else:
            return "({} {} {})".format(self.operator, self.left_member.id, self.right_member)


class AtLeast:
    """
    At Least defined by:
    - a minimum k
    - a list of inequalities
    """

    def __init__(self, k, inequalities):
        self.k = k
        self.inequalities = inequalities

    def __str__(self):
        """ At least to logic format.
        """
        text = ">=_{} (".format(self.k)
        for index, ineq in enumerate(self.inequalities):
            text += str(ineq)
            if index != len(self.inequalities) - 1:
                text += ", "
        text += ")"
        return text

    def smtlib(self, k=None):
        """ Inequality.
            SMT-LIB format
        """
        smt_input = "((_ at-least {}) ".format(self.k)
        for ineq in self.inequalities:
            smt_input += ineq.smtlib(k)
        smt_input += ")"
        return smt_input


if __name__ == '__main__':

    if len(sys.argv) == 1:
        exit("File missing: ./formula <path_to_net> <path_to_xml")

    pn = PetriNet(sys.argv[1])
    props = Properties(pn, sys.argv[2])

    print("Logic Formula")
    print("-------------")
    print(props)

    print("\nSMTlib2 Format")
    print("--------------")
    print(props.smtlib())
