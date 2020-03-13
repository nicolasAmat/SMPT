#!/usr/bin/env python3

"""
Formula Generator and Solver Module
"""

from pn import PetriNet

import sys


class Formula:
    """
    Formula defined by:
    - a Petri Net
    - a set of clauses
    - a property (deadlock)
    """
    def __init__(self, pn, prop = "deadlock"):
        self.pn = pn
        self.clauses = []
        self.prop = prop
        if prop == "deadlock":
            self.generate_deadlock()

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

    def generate_deadlock(self):
        for tr in self.pn.transitions.values():
            inequalities = []
            for pl, weight in tr.src.items():
                if weight > 0:
                    ineq = Inequality(pl, weight, '<')
                else:
                    ineq = Inequality(pl, - weight, '>=')
                inequalities.append(ineq)
            self.clauses.append(Clause(inequalities))

    def check_sat(self, solver):
        solver.stdin.write(bytes("(check-sat)\n", 'utf-8'))
        solver.stdin.flush()
        if solver.stdout.readline().decode('utf-8').strip() == 'sat':
            return 1
        return 0

    def get_model(self, solver):
        solver.stdin.write(bytes("(get-model)\n", 'utf-8'))
        solver.stdin.flush()
        
        model = ""

        # Read the model
        solver.stdout.readline()
        # Parse the model
        while True:
            place_content = solver.stdout.readline().decode('utf-8').strip().split(' ')
            if len(place_content) < 2 or solver.poll() is not None:
                break
            place_marking =  solver.stdout.readline().decode('utf-8').strip().replace(' ', '').replace(')', '')
            if (place_marking and int(place_marking) > 0) and place_content[1] in self.pn.places:
                model += ' ' + place_content[1]

        print("The input Petri Net can deadlock!")
        
        if model == "":
            model = " empty marking"
        print("Model:{}".format(model))
        
        return 1
    
    def result(self, solver):
        if solver.stdout.readline().decode('utf-8').strip() == 'unsat':
            print("The input Petri Net is deadlock free.")
        else:
            model = ""

            # Read the model
            solver.stdout.readline()

            # Parse the model
            while True:
                place_content = solver.stdout.readline().decode('utf-8').strip().split(' ')
                place_marking =  solver.stdout.readline().decode('utf-8').strip().replace(' ', '').replace(')', '')
                if len(place_content) < 2 and solver.poll() is not None:
                    break
                if (place_marking and int(place_marking) > 0) and place_content[1] in self.pn.places:
                    model += ' ' + place_content[1]
 
            print("The input Petri Net can deadlock!")
            
            if model == "":
                model = " empty marking"
            print("Model:{}".format(model))


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


class Inequality:
    """
    Inequality defined by:
    - a left member
    - a right member
    - an operator (=, <=, >=, <, >)
    """
    def __init__(self, left_member, right_member, operator):
        self.left = left_member
        self.right = right_member
        self.operator = operator

    def __str__(self):
        return "{} {} {}".format(self.left.id, self.operator, self.right)

    def smtlib(self):
        return "({} {} {})".format(self.operator, self.left.id, self.right)


if __name__ == '__main__':
    
    if len(sys.argv) == 1:
        exit("File missing: ./formula <path_to_file>")
    
    net = PetriNet(sys.argv[1])
    phi = Formula(net)
    
    print("Logic Formula")
    print("-------------")
    print(phi)
    
    print("\nSMTlib2 Format")
    print("--------------")
    print(phi.smtlib())
