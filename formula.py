#!/usr/bin/env python3

"""
Formula Generator
"""

from pn import *
import sys

class Inequality:
    """
    Inequality defined by:
    - a left member
    - a right member
    - an operator (=, <=, >=, <, >)
    """
    def __init__(self, leftMember, rightMember, operator):
        self.left = leftMember
        self.right = rightMember
        self.operator = operator

    def __str__(self):
        return "{} {} {}".format(self.left.id, self.operator, self.right)

    def smtlib(self):
        return "({} {} {})".format(self.operator, self.left.id, self.right)

class Clause:
    """
    Clause defined by:
    - a set of inequalities
    """
    def __init__(self, inequalities):
        self.inequalities = inequalities

    def __str__(self):
        text = ""
        for index, ineq in enumerate(self.inequalities):
            text += str(ineq)
            if index != len(self.inequalities) - 1:
                text += " or "
        return text

    def smtlib(self):
        text = "(assert (or "
        for ineq in self.inequalities:
            text += ineq.smtlib()
        text += "))"
        return text


class Formula:
    def __init__(self, pn, prop = "deadlock"):
        self.pn = pn
        self.clauses = []
        self.prop = prop
        if prop == "deadlock":
            self.deadlock()

    def __str__(self):
        text = ""
        for index, clause in enumerate(self.clauses):
            text += "(" + str(clause) + ")"
            if index != len(self.clauses) - 1:
                text += " and "
        return text

    def smtlib(self):
        text = ""
        for clause in self.clauses:
            text += clause.smtlib() + '\n'
        return text

    def deadlock(self):
        for tr in self.pn.transitions.values():
            inequalities = []
            for src in tr.src:
                ineq = Inequality(src, 1, '<')
                inequalities.append(ineq)
            self.clauses.append(Clause(inequalities))

    def result(self, solver):
        if (solver.stdout.readline().decode('utf-8').strip() == 'unsat'):
            print("The input Petri Net is deadlock free.")
        else:
            model = ""

            # Read the model
            solver.stdout.readline()

            # Parse the model and fill the grid
            while(True):
                place_content = solver.stdout.readline().decode('utf-8').strip().split(' ')
                place_marking =  solver.stdout.readline().decode('utf-8').strip().replace(' ', '').replace(')', '')
                if len(place_content) < 2 and solver.poll() is not None:
                    break
                if (place_marking and int(place_marking) > 0) and place_content[1] in self.pn.places:
                    model += ' ' + place_content[1]

            print("The input Petri Net can deadlock!")
            print("Model:{}".format(model))

if __name__=='__main__':
    if (len(sys.argv) == 1):
        exit("File missing: ./formula <path_to_file>")
    net = PetriNet(sys.argv[1])
    phi = Formula(net)
    print("Logic Formula")
    print("-------------")
    print(phi)
    print("\nSMTlib2 Format")
    print("--------------")
    print(phi.smtlib())
