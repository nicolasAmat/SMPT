#!/usr/bin/env python3

"""
Linear Equations Parser

File format: .net
Documentation: http://projects.laas.fr/tina//manuals/formats.html
"""

import sys

class System:
    """
    Equation system
    """
    def __init__(self, filename):
        self.system = []
        self.parser(filename)

    def __str__(self):
        text = ""
        for eq in self.system:
            text += str(eq) + '\n'
        return text

    def smtlib(self):
        text = ""
        for eq in self.system:
            text += eq.smtlib() + '\n'
        return text

    def parser(self, filename):
        try:
            with open(filename, 'r') as fp:
                eq = False

                for line in fp.readlines():
                    
                    content = line.strip().split(' ')
                    if content.pop(0) != '#':
                        eq = False
                    
                    if eq:
                        lRead = False
                        rRead = False

                        leftMembers = []
                        rightMembers = []
                        operator = ""

                        for element in content:
                            if element == '|-':
                                lRead = True
                            elif element != '+':
                                if element == '=':
                                    operator = element
                                    lRead = False
                                    rRead = True
                                elif lRead:
                                    leftMembers.append(element)
                                elif rRead:
                                    rightMembers.append(element)

                        self.system.append(Equation(leftMembers, rightMembers, operator))

                    if "# generated equations" in line:
                        eq = True
            fp.close()
        except FileNotFoundError as e:
            exit(e)        

class Equation:
    """
    Equation defined by:
    - Left members
    - Right members
    - Operator
    """
    def __init__(self, leftMembers, rightMembers, operator):
        self.left = leftMembers
        self.right = rightMembers
        self.operator = operator

    def __str__(self):
        text = ""
        for lMember in self.left:
            text += lMember + " "
        text += self.operator + " "
        for rMember in self.right:
            text += rMember + " "
        return text

    def smtlib(self):
        text = "(assert ({}".format(self.operator)
        if len(self.left) > 1:
            text += " (+"
        for member in self.left:
            text += " {}".format(member)
        if len(self.left) > 1:
            text += ")"
        if len(self.right) > 1:
            text += " (+"
        for member in self.right:
            text += " {}".format(member)
        if len(self.right) > 1:
            text += ")"
        text += "))"
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
