#!/usr/bin/env python3

"""
Enumerative Marking Module

Input file format: .aut
Documentation: http://projects.laas.fr/tina//manuals/formats.html
"""

from pn import PetriNet
from formula import Properties
from eq import System

import re
import sys
from subprocess import PIPE, Popen
from threading import Thread, Event


class EnumerativeMarking:
    """
    Marking defined by:
    - a Petri Net
    - a set of reachable markings
    """
    def __init__(self, filename, pn, pn_reduced, eq, formula):
        self.pn = pn
        self.pn_reduced = pn_reduced
        self.eq = eq
        self.formula = formula
        self.markings = []
        self.parse_markings(filename)
        self.solver = Popen(["z3", "-in"], stdin = PIPE, stdout=PIPE)
        

    def __str__(self):
        text = ""
        for marking in self.markings:
            text += "-> "
            for place, counter in marking.items():
                text += "{}:{} ".format(place, counter)
            text += "\n"
        return text

    def smtlib(self):
        text = ""
        text += "(assert (or "
        for marking in self.markings:
            text += "(and "
            for place, counter in marking.items():
                text += "(= {} {})". format(place, counter)
            for place in self.pn_reduced.places:
                if place not in marking:
                    text += "(= {} 0)". format(place)
            text += ")"
        text += "))\n"
        return text

    def parse_markings(self, filename):
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = line.strip().replace('(', '').replace(')', '').split(',')
                    if content[0] == content[-1]:
                        places = re.split(r'\s+', content[1].replace('"', ''))
                        consistent = True
                        marking = dict()
                        for place in places:
                            place_data = place.split('.')
                            if place_data[0] != 'S':
                                consistent = False
                                break
                            marking[place_data[1].replace('`', '').replace('{', '').replace('}', '')] = 1
                        if consistent:
                            self.markings.append(marking)
        except FileNotFoundError as e:
            exit(e)

    def solve(self):
        smt_input = "; Variable Definitions\n" \
            + self.pn.smtlib_declare_places()  \
            + "; Reduction Equations\n"        \
            + self.eq.smtlib()                 \
            + "; Property Formula\n"           \
            + self.formula.smtlib()            \
            + "; Reduced Net Markings\n"       \
            + self.smtlib()
        
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        self.solver.stdin.flush()
        
        if self.formula.check_sat(self.solver):
            self.formula.get_model(self.solver)
        else:
            print("Property not verified!")



if __name__ == '__main__':

    if len(sys.argv) != 3:
        exit("File missing: ./enumerativemarking <path_to_net_file> <path_to_aut_file>")

    net = PetriNet(sys.argv[1])
    markings = EnumerativeMarking(sys.argv[2], None, net, None, None)

    print("Markings Enumeration")
    print("--------------------")
    print(markings)

    print("\nSMTlib2 Format")
    print("--------------")
    print(markings.smtlib())
