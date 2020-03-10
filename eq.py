#!/usr/bin/env python3

"""
Linear System Module

Input file format: .net
"""

import sys
import re

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
        self.additionalVars = []
        self.system = []
        self.parser(filename)

    def __str__(self):
        text = ""
        for eq in self.system:
            text += str(eq) + '\n'
        return text

    def smtlib(self):
        text = ""
        for var in self.additionalVars:
            text += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var)
        for eq in self.system:
            text += eq.smtlib() + '\n'
        return text

    def smtlibOnlyNonReducedPlaces(self):
        text = ""
        for var in self.additionalVars:
            if var not in self.places_reduced:
                text += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var)
        for eq in self.system:
            if not eq.contain_reduced:
                text += eq.smtlib() + '\n'
        return text
        
    def smtlibOrdered(self, k):
        text = ""
        for eq in self.system:
            if eq.contain_reduced:
                text += eq.smtlibOrdered(k, self.places_reduced) + '\n'
        for pl in self.places_reduced:
            if pl in self.places:
                text += "(assert (= {}@{} {}))\n".format(pl, k, pl)
        return text

    def parser(self, filename):
        try:
            with open(filename, 'r') as fp:
                lines = re.split('\n+', re.search(r'# generated equations\n(.*)?\n\n', fp.read(), re.DOTALL).group())[1:-1]
                equations = [re.split('\s+', line.partition(' |- ')[2]) for line in lines]
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
        self.parseEquation(eq, system)

    def __str__(self):
        return self.memberStr(self.left) + '= ' + self.memberStr(self.right)

    def memberStr(self, member):
        text = ""
        for index, elem in enumerate(member):
            text += elem + " "
            if index != len(member) - 1:
                text += '+ '
        return text

    def smtlib(self):
        return "(assert ({}".format(self.operator) + self.memberSmtlib(self.left) + self.memberSmtlib(self.right) + "))"

    def memberSmtlib(self, member):
        text = "" 
        if len(member) > 1:
            text += " (+"
        for elem in member:
            text += " {}".format(elem)
        if len(member) > 1:
            text += ")"
        return text

    def smtlibOrdered(self, k, places_reduced):
        return "(assert ({}".format(self.operator) + self.memberSmtlibOrdered(self.left, k, places_reduced) + self.memberSmtlibOrdered(self.right, k, places_reduced) + "))"

    def memberSmtlibOrdered(self, member, k, places_reduced = []):
        text = "" 
        if len(member) > 1:
            text += " (+"
        for elem in member:
            if elem in places_reduced:
                text += " {}@{}".format(elem, k)
            else:
                text += " {}".format(elem)
        if len(member) > 1:
            text += ")"
        return text

    def parseEquation(self, eq, system):
        left = True
        for element in eq:
            if element != '+':
                if element in ['=', '<=', '>=', '<', '>']:
                    self.operator = element
                    left = False
                else:
                    element = element.replace('{', '').replace('}', '').replace('#', '')
                    if not element.isnumeric():
                        if element not in system.places and element not in system.additionalVars:
                            system.additionalVars.append(element)
                        if element in system.places_reduced:
                            self.contain_reduced = True
                    if left:
                        self.left.append(element)
                    else:
                        self.right.append(element)


if __name__ == "__main__":
    
    if (len(sys.argv) == 1):
        exit("File missing: ./eq <path_to_file>")
    
    system = System(sys.argv[1])
    
    print("Equations")
    print("---------")
    print(system)
    
    print("\nSMTlib2 Format")
    print("--------------")
    print(system.smtlib())
