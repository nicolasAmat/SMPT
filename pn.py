#!/usr/bin/env python3

"""
Petri Net Module

Input file format: .net
Documentation: http://projects.laas.fr/tina//manuals/formats.html
"""

import sys
import re

class PetriNet:
    """
    Petri Net defined by:
    - an identifier
    - a finite set of places (identified by names)
    - a finite set of transitions (identified by names)
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

    def smtlibDeclarePlaces(self):
        text = ""
        for place in self.places.values():
            text += place.smtlibDeclare()
        return text

    def smtlibDeclarePlacesOrdered(self, k):
        text = ""
        for place in self.places.values():
            text += place.smtlibDeclareOrdered(k)
        return text

    def smtlibSetMarkingOrdered(self, k):
        text = ""
        for pl in self.places.values():
            text += pl.smtlibSetMarkingOrdered(k)
        return text

    def smtlibTransitionsOrdered(self, k):
        text = "(assert (or \n"
        for tr in self.transitions.values():
            text += tr.smtlibOrdered(k)
        text += "))\n"
        return text

    def parseNet(self, filename):
            try:
                with open(filename, 'r') as fp:
                    for line in fp.readlines():
                        content = re.split('\s+', line.strip().replace('#', ''))
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
        tr_id = content.pop(0)
        
        if tr_id in self.transitions:
            tr = self.transitions[tr.id]
        else:
            tr = Transition(tr_id, self)
            self.transitions[tr.id] = tr

        content = self.parseLabel(content)

        arrow = content.index("->")
        src = content[0:arrow]
        dst = content[arrow + 1:]

        for pl in src:
            arc = self.parseArc(pl)
            tr.src.append(arc)
            tr.pl_linked.append(arc[0])

        for pl in dst:
            arc = self.parseArc(pl)
            tr.dest.append(arc)
            tr.pl_linked.append(arc[0])

    def parseArc(self, pl):
        pl = pl.replace('{', '').replace('}', '').split('*')
        
        if pl[0] not in self.places:
            self.places[pl[0]] = Place(pl[0])
        if len(pl) == 1:
            weight = 1
        else:
            weight = int(pl[1])
        return (self.places.get(pl[0]), weight)

    def parsePlace(self, content):
        place_id = content.pop(0).replace('{', '').replace('}', '')
        
        content = self.parseLabel(content)

        if len(content) == 1:
            marking = content[0].replace('(', '').replace(')', '')
        else:
            marking = 0

        if place_id not in self.places:
            self.places[place_id] = Place(place_id, marking)
        else:
            self.places.get(place_id).marking = marking

    def parseLabel(self, content):
        index_pl = 0
        if content[index_pl] == ':':
            label_skipped = content[index_pl + 1][0] != '{'
            index_pl = 2
            while not label_skipped:
                label_skipped = content[index_pl][-1] == '}'             
                index_pl += 1
        return content[index_pl:]

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

    def smtlibDeclare(self):
        return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.id, self.id)

    def smtlibDeclareOrdered(self, k):
        return "(declare-const {}@{} Int)\n(assert (>= {}@{} 0))\n".format(self.id, k, self.id, k)

    def smtlibSetMarkingOrdered(self, k):
        return "(assert (= {}@{} {}))\n".format(self.id, k, self.marking)

class Transition:
    """
    Transition defined by:
    - an identifier
    - a list of input places
    - a list of output places
    """
    def __init__(self, id, pn):
        self.id = id
        self.pn = pn
        self.src = []
        self.dest = []
        self.pl_linked = []

    def __str__(self):
        text = "tr {}  ".format(self.id)
        for src in self.src:
            text += self.strArc(src)
        text += '-> '
        for dest in self.dest:
            text += self.strArc(dest)
        text += '\n'
        return text

    def strArc(self, pl):
        text = ""
        text += pl[0].id
        if len(pl) == 2:
            text += '*' + str(pl[1])
        text += ' '
        return text

    def smtlibOrdered(self, k):
        text = "\t(and\n\t\t(=>\n\t\t\t(and "
        for arc in self.src:
            text += "(>= {}@{} {})".format(arc[0].id, k, arc[1])
        text += ")\n\t\t\t(and "
        for arc in self.src:
            text += "(= {}@{} (- {}@{} {}))".format(arc[0].id, k + 1, arc[0].id, k, arc[1])
        for arc in self.dest:
            text += "(= {}@{} (+ {}@{} {}))".format(arc[0].id, k + 1, arc[0].id, k, arc[1])
        for pl in self.pn.places.values():
            if pl not in self.pl_linked:
                text += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        text += ")\n\t\t)\n\t\t(=>\n\t\t\t(or "
        for arc in self.src:
            text += "(< {}@{} {})".format(arc[0].id, k, arc[1])
        text += ")\n\t\t\t(and "
        for pl in self.pn.places.values():
            text += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        text += ")\n\t\t)\n\t)\n"
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
    print(net.smtlibDeclarePlaces())
