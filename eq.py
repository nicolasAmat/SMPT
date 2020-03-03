#!/usr/bin/env python3

"""
Linear System Parser

Input file format: .net
"""

import sys
import re

class System:
    """
    Equation system defined by:
    - a set of places from the original Petri Net
    - a set of additional variables
    - a set of equations / inequations
    """
    def __init__(self, filename, places = []):
        self.places = places
        self.system = []
        self.additionalVars = []
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

    def parser(self, filename):
        try:
            with open(filename, 'r') as fp:
                lines = re.split('\n+', re.search(r'# generated equations\n(.*)?\n\n', fp.read(), re.DOTALL).group())[1:-1]
                equations = [re.split('\s+', line.partition(' |- ')[2]) for line in lines]

                for eq in equations:
                    left = True

                    leftMembers = []
                    rightMembers = []
                    operator = ""

                    for element in eq:
                        if element != '+':
                            if element in ['=', '<=', '>=', '<', '>']:
                                operator = element
                                left = False
                            else:
                                element = element.replace('{', '').replace('}', '').replace('#', '')
                                if not element.isnumeric() and element not in self.places and element not in self.additionalVars:
                                    self.additionalVars.append(element)
                                if left:
                                    leftMembers.append(element)
                                else:
                                    rightMembers.append(element)

                    self.system.append(Equation(leftMembers, rightMembers, operator))

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
    def __init__(self, leftMember, rightMember, operator):
        self.left = leftMember
        self.right = rightMember
        self.operator = operator

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
