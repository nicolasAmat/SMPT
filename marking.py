#!/usr/bin/env python3

"""
Enumerative Marking Module

Input file format: .aut
Documentation: http://projects.laas.fr/tina//manuals/formats.html
"""

from pn import PetriNet

import re
import sys

class Marking:
    """
    Marking defined by:
    - a Petri Net
    - a set of reachable markings
    """
    def __init__(self, filename, pn):
        self.pn = pn
        self.markings = []
        self.parseMarkings(filename)

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
            for place in self.pn.places:
                if place not in marking:
                    text += "(= {} 0)". format(place)
            text += ")"
        text += "))\n"
        return text

    def parseMarkings(self, filename):
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = line.strip().replace('(', '').replace(')', '').split(',')
                    if content[0] == content[-1]:
                        places = re.split('\s+', content[1].replace('"', ''))
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


if __name__=='__main__':

    if (len(sys.argv) != 3):
        exit("File missing: ./marking <path_to_aut_file> <path_to_net_file>")

    net = PetriNet(sys.argv[2])
    marks = Marking(sys.argv[1], net)

    print("Markings Enumeration")
    print("--------------------")
    print(marks)

    print("\nSMTlib2 Format")
    print("--------------")
    print(marks.smtlib())
