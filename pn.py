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
        self.parse_net(filename)

    def __str__(self):
        text = "net {}\n".format(self.id)
        for pl in self.places.values():
            text += str(pl)
        for tr in self.transitions.values():
            text += str(tr)
        return text

    def smtlib_declare_places(self):
        text = ""
        for place in self.places.values():
            text += place.smtlib_declare()
        return text

    def smtlib_declare_places_ordered(self, k):
        text = ""
        for place in self.places.values():
            text += place.smtlib_declare_ordered(k)
        return text

    def smtlib_set_marking_ordered(self, k):
        text = ""
        for pl in self.places.values():
            text += pl.smtlib_set_marking_ordered(k)
        return text

    def smtlib_transitions_ordered(self, k):
        text = "(assert (or \n"
        for tr in self.transitions.values():
            text += tr.smtlib_ordered(k)
        text += "))\n"
        return text

    def parse_net(self, filename):
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = re.split(r'\s+', line.strip().replace('#', ''))
                    element = content.pop(0)
                    if element == "net":
                        self.id = content[0]
                    if element == "tr":
                        self.parse_transition(content)
                    if element == "pl":
                        self.parse_place(content)
            fp.close()
        except FileNotFoundError as e:
            exit(e)

    def parse_transition(self, content):
        tr_id = content.pop(0)
        
        if tr_id in self.transitions:
            tr = self.transitions[tr.id]
        else:
            tr = Transition(tr_id, self)
            self.transitions[tr.id] = tr

        content = self.parse_label(content)

        arrow = content.index("->")
        src = content[0:arrow]
        dst = content[arrow + 1:]

        for arc in src:
            tr.pl_linked.append(self.parse_arc(arc, tr.src, tr.dest))

        for arc in dst:
            tr.pl_linked.append(self.parse_arc(arc, tr.dest))

    def parse_arc(self, arc, arcs, opposite_arcs = []):
        arc = arc.replace('{', '').replace('}', '')

        test_arc, inhibitor_arc = False, False 

        if '?-' in arc:
            inhibitor_arc = True
            arc = arc.split('?-')
        elif '?' in arc:
            test_arc = True
            arc = arc.split('?')
        elif '*' in arc:
            arc = arc.split('*')
        else:
            arc = [arc]

        if arc[0] not in self.places:
            self.places[arc[0]] = Place(arc[0])
        
        if len(arc) == 1:
            weight = 1
        else:
            weight = int(arc[1])
        
        if inhibitor_arc:
            weight = -weight

        pl = self.places.get(arc[0])
        arcs[pl] = weight

        if test_arc:
            opposite_arcs[pl] = weight
        
        return pl

    def parse_place(self, content):
        place_id = content.pop(0).replace('{', '').replace('}', '')
        
        content = self.parse_label(content)

        if len(content) == 1:
            marking = content[0].replace('(', '').replace(')', '')
        else:
            marking = 0

        if place_id not in self.places:
            self.places[place_id] = Place(place_id, marking)
        else:
            self.places.get(place_id).marking = marking

    def parse_label(self, content):
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

    def smtlib_declare(self):
        return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.id, self.id)

    def smtlib_declare_ordered(self, k):
        return "(declare-const {}@{} Int)\n(assert (>= {}@{} 0))\n".format(self.id, k, self.id, k)

    def smtlib_set_marking_ordered(self, k):
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
        self.src = {}
        self.dest = {}
        self.pl_linked = []

    def __str__(self):
        text = "tr {}  ".format(self.id)
        for src, weight in self.src.items():
            text += self.str_arc(src, weight)
        text += '-> '
        for dest, weight in self.dest.items():
            text += self.str_arc(dest, weight)
        text += '\n'
        return text

    def str_arc(self, pl, weight):
        text = ""
        text += pl.id
        if weight > 1:
            text += '*' + str(weight)
        if weight < 0:
            text += '?-' + str(- weight)
        text += ' '
        return text

    def smtlib_ordered(self, k):
        text = "\t(and\n\t\t(=>\n\t\t\t(and "
        for pl, weight in self.src.items():
            if weight > 0:
                text += "(>= {}@{} {})".format(pl.id, k, weight)
            else:
                text += "(< {}@{} {})".format(pl.id, k, - weight)
        text += ")\n\t\t\t(and "
        for pl, weight in self.src.items():
            if weight > 0:
                if pl in self.dest:
                    text += "(= {}@{} (- (+ {}@{} {}) {}))".format(pl.id, k + 1, pl.id, k, self.dest[pl], weight)
                else:
                    text += "(= {}@{} (- {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        for pl, weight in self.dest.items():
            if pl not in self.src or self.src[pl] < 0:
                text += "(= {}@{} (+ {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        for pl in self.pn.places.values():
            if pl not in self.pl_linked:
                text += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        text += ")\n\t\t)\n\t\t(=>\n\t\t\t(or "
        for pl, weight in self.src.items():
            if weight > 0:
                text += "(< {}@{} {})".format(pl.id, k, weight)
            else:
                text += "(>= {}@{} {})".format(pl.id, k, - weight)
        text += ")\n\t\t\t(and "
        for pl in self.pn.places.values():
            text += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        text += ")\n\t\t)\n\t)\n"
        return text


if __name__ == "__main__":
    
    if len(sys.argv) == 1:
        exit("File missing: ./pn <path_to_file>")
    
    net = PetriNet(sys.argv[1])
    
    print("Petri Net")
    print("---------")
    print(net)
    
    print("SMTlib")
    print("------")
    print(net.smtlib_declare_places())
