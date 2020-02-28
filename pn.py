#!/usr/bin/env python3

"""
Petri Net Parser

Input file format: .net
Documentation: http://projects.laas.fr/tina//manuals/formats.html
"""

import sys
import re

class PetriNet:
    """
    Petri Net defined by:
    - an identifier
    - a finite set of places
    - a finite set of transitions
    """
    def __init__(self, filename):
        self.id = ""
        self.places = {}
        self.transitions = {}
        self.parseNet(filename)

    def __str__(self):
        text = "net {}\n".format(self.id)
        for pl in self.places.values():
            text += str(pl)
        for tr in self.transitions.values():
            text += str(tr)
        return text

    def smtlib(self):
        text = ""
        for place in self.places.values():
            text += place.smtlib()
        return text

    def parseNet(self, filename):
            try:
                with open(filename, 'r') as fp:
                    for line in fp.readlines():
                        content = re.split('\s+', line.strip())
                        element = content.pop(0)
                        if element == "net":
                            self.id = content[0]
                        if element == "tr":
                            self.parseTransition(content)
                        if element == "pl":
                            self.parsePlace(content)
                fp.close()
            except FileNotFoundError as e:
                exit(e)

    def parseTransition(self, content):
        tr = Transition(content[0])
        self.transitions[tr.id] = tr
        
        arrow = content.index("->")
        src = content[1:arrow]
        dst = content[arrow + 1:]

        for pl in src:
            if pl not in self.places:
                self.places[pl] = Place(pl)
            tr.src.append(self.places.get(pl))

        for pl in dst:
            if pl not in self.places:
                self.places[pl] = Place(pl)
            tr.dest.append(self.places.get(pl))

    def parsePlace(self, content):
        placeId = content[0]
        marking = content[1].replace('(', '').replace(')', '')
    
        if placeId not in self.places:
            self.places[placeId] = Place(placeId, marking)
        else:
            self.places.get(placeId).marking = marking

class Place:
    """
    Place defined by:
    - an identifier
    - a marking
    """
    def __init__(self, id, marking = 0):
        self.id = id
        self.marking = marking

    def __str__(self):
        text = ""
        if self.marking:
            text = "pl {} ({})\n".format(self.id, self.marking)
        return text

    def smtlib(self):
        return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.id, self.id)

class Transition:
    """
    Transition defined by:
    - an identifier
    - a list of input places
    - a list of output places
    """
    def __init__(self, id):
        self.id = id
        self.src = []
        self.dest = []

    def __str__(self):
        text = "tr {}  ".format(self.id)
        for src in self.src:
            text += src.id + " "
        text += '-> '
        for dest in self.dest:
            text += dest.id + " "
        text += '\n'
        return text


if __name__ == "__main__":
    
    if (len(sys.argv) == 1):
        exit("File missing: ./pn <path_to_file>")
    net = PetriNet(sys.argv[1])
    print("Petri Net")
    print("---------")
    print(net)
    print("SMTlib")
    print("------")
    print(net.smtlib())
