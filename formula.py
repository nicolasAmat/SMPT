#!/usr/bin/env python3

"""
Formula Generator and Solver Module
"""

from pn import PetriNet

import sys
import re
import xml.etree.ElementTree as ET


class Properties:
    """
    Properties parsed from .xml file defined by:
    - a set of Formulas
    """
    def __init__(self, pn, xml_filename):
        self.pn = pn
        self.formulas = {}
        self.parseXML(xml_filename)

    def __str__(self):
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "--- Property {} ---\n".format(formula_id)
            text += str(formula)
        return text
    
    def smtlib(self):
        text = ""
        for formula_id, formula in self.formulas.items():
            text += "; {}\n".format(formula_id)
            text += formula.smtlib()
        return text

    def parseXML(self, filename):
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

            deadlock = prop_formula.find('./' + namespace + 'exists-path/'+ namespace + 'finally/' + namespace + 'deadlock')
            fireability = prop_formula.find('./' + namespace + 'exists-path/'+ namespace + 'finally/' + namespace + 'is-fireable')

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
    - a Petri Net
    - a set of clauses
    - a property (deadlock)
    """
    def __init__(self, pn, prop = 'deadlock', transitions = []):
        self.pn = pn
        self.clauses = []
        self.operator = ""
        self.prop = prop
        if prop == 'deadlock':
            self.generate_deadlock()
        if prop == 'fireability':
            self.generate_fireability(transitions)
        if prop == 'reachability':
            # Start Debug
            marking = {}
            marking[self.pn.places["Pout3"]] = 1
            # End Debug
            self.generate_reachability(marking)

    def __str__(self):
        text = ""
        for index, clause in enumerate(self.clauses):
            text += "(" + str(clause) + ")"
            if index != len(self.clauses) - 1:
                text += " and "
        text += "\n"
        return text

    def smtlib(self, k = None):
        if self.operator == "or":
            return self.disjunctive_smtlib(k)
        else:
            return self.conjunctive_smtlib(k)

    def conjunctive_smtlib(self, k = None):
        text = ""
        for clause in self.clauses:
            text += "(assert {})\n".format(clause.smtlib(k))
        return text

    def disjunctive_smtlib(self, k = None):
        text = "(assert (or "
        for clause in self.clauses:
            text += clause.smtlib(k)
        text += "))\n"
        return text

    def generate_deadlock(self):
        for tr in self.pn.transitions.values():
            inequalities = []
            for pl, weight in tr.src.items():
                if weight > 0:
                    ineq = Inequality(pl, weight, '<')
                else:
                    ineq = Inequality(pl, - weight, '>=')
                inequalities.append(ineq)
            self.clauses.append(Clause(inequalities, "or"))
        self.operator = "and"

    def generate_fireability(self, transitions):
        for tr_id in transitions:
            inequalities = []
            tr = self.pn.transitions[tr_id]
            for pl, weight in tr.src.items():
                if weight > 0:
                    ineq = Inequality(pl, weight, '>=')
                else:
                    ineq = Inequality(pl, - weight, '<')
                inequalities.append(ineq)
            self.clauses.append(Clause(inequalities, "and"))
        self.operator = "or"

    def generate_reachability(self, marking):
        for pl, counter in marking.items():
    def result(self, sat):
        if self.prop == "deadlock":
            if sat:
                print("Deadlock.")
            else:
                print("Deadlockless")
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
        self.inequalities = inequalities
        self.operator = operator

    def __str__(self):
        text = ""
        for index, ineq in enumerate(self.inequalities):
            text += str(ineq)
            if index != len(self.inequalities) - 1:
                text += " " + self.operator + " "
        return text

    def smtlib(self, k = None, write_assert = False, neg = False):
        text = ""
        for ineq in self.inequalities:
            text += ineq.smtlib(k)
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
        self.left_member = left_member
        self.right_member = right_member
        self.operator = operator

    def __str__(self):
        return "{} {} {}".format(self.left_member.id, self.operator, self.right_member)

    def smtlib(self, k = None):
        if k is not None:
            return "({} {}@{} {})".format(self.operator, self.left_member.id, k, self.right_member)
        else:
            return "({} {} {})".format(self.operator, self.left_member.id, self.right_member)


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
