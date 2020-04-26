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

        self.counter_places = 0
        self.ordered_places = []

        self.parse_net(filename)

    def __str__(self):
        """ Petri Net to .net format.
        """
        text = "net {}\n".format(self.id)
        for pl in self.places.values():
            text += str(pl)
        for tr in self.transitions.values():
            text += str(tr)
        return text

    def smtlib_declare_places(self, k=None):
        """ Declare places.
            SMT-LIB format
        """
        smt_input = ""
        for place in self.places.values():
            smt_input += place.smtlib_declare(k)
        return smt_input

    def smtlib_set_marking(self, k=None):
        """ Assertions to set the initial marking on places.
            SMT-LIB format
        """
        smt_input = ""
        for pl in self.places.values():
            smt_input += pl.smtlib_set_marking(k)
        return smt_input

    def smtlib_transitions(self, k):
        """ Transition relations from places at order k to order k + 1.
            SMT-LIB format
        """
        smt_input = "(assert (or \n"
        for tr in self.transitions.values():
            smt_input += tr.smtlib(k)
        smt_input += "\t(and\n\t\t"
        for pl in self.places.values():
            smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        smt_input += "\n\t)\n))\n"
        return smt_input

    def smtlib_transitions_textbook(self, k):
        """ Transition relations from places at order k to order k + 1.
            Textbook version not used.
            SMT-LIB format
        """
        smt_input = "(assert (or \n"
        for tr in self.transitions.values():
            smt_input += tr.smtlib_textbook(k)
        smt_input += "))\n"
        return smt_input

    def parse_net(self, filename):
        """ Petri Net parser.
            Input format: .net
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = re.split(r'\s+', line.strip().replace('#', '')) # '#' is forbidden in SMT-LIB
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
        """ Transition parser.
            Input format: .net
        """
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
            tr.pl_linked.append(self.parse_arc(arc, tr.input, tr.output))

        for arc in dst:
            tr.pl_linked.append(self.parse_arc(arc, tr.output))

    def parse_arc(self, arc, arcs, opposite_arcs = []):
        """ Arc parser.
            Can handle:
                - Normal Arc
                - Test Arc
                - Inhibitor Arc
            Input format: .net
        """
        arc = arc.replace('{', '').replace('}', '') # '{' and '}' are forbidden in SMT-LIB

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

        place_id = arc[0]

        if place_id not in self.places:
            new_place = Place(place_id, self.counter_places)
            self.places[place_id] = new_place
            self.ordered_places.append(new_place)
            self.counter_places += 1
        
        if len(arc) == 1:
            weight = 1
        else:
            weight = int(arc[1])
        
        # To recognize an inhibitor arc, we set a negative weight
        if inhibitor_arc:
            weight = -weight

        pl = self.places.get(place_id)
        arcs[pl] = weight

        # In a case of a test arc, we add a second arc 
        if test_arc:
            opposite_arcs[pl] = weight
        
        return pl

    def parse_place(self, content):
        """ Place parser.
            Input format: .net
        """
        place_id = content.pop(0).replace('{', '').replace('}', '') # '{' and '}' are forbidden in SMT-LIB
        
        content = self.parse_label(content)

        if len(content) == 1:
            marking = int(content[0].replace('(', '').replace(')', ''))
        else:
            marking = 0

        if place_id not in self.places:
            new_place = Place(place_id, self.counter_places, marking)
            self.places[place_id] = new_place
            self.ordered_places.append(new_place)
            self.counter_places += 1
        else:
            self.places.get(place_id).marking = marking

    def parse_label(self, content):
        """ Label parser.
            Input format: .net
        """
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
    - an initial marking
    - an order
    """
    def __init__(self, pl_id, order, marking=0):
        self.id = pl_id
        self.marking = marking
        self.order = order

    def __str__(self):
        """ Place to .net format.
        """
        text = ""
        if self.marking:
            text = "pl {} ({})\n".format(self.id, self.marking)
        return text

    def smtlib_declare(self, k=None):
        """ Declare a place.
            SMT-LIB format
        """
        if k is not None:
            return "(declare-const {}@{} Int)\n(assert (>= {}@{} 0))\n".format(self.id, k, self.id, k)
        else:
            return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.id, self.id)

    def smtlib_set_marking(self, k=None):
        """ Assertions to set the initial marking.
            SMT-LIB format
        """
        if k is not None:
            return "(assert (= {}@{} {}))\n".format(self.id, k, self.marking)
        else:
            return "(assert (= {} {}))\n".format(self.id, self.marking)


class Transition:
    """
    Transition defined by:
    - an identifier
    - a set of input places (keys),
      associated to the weight of the arc (values)
    - a list of output places (keys),
      associated to the weight of the arc (values)
    - the set of all the places linked to the transition,

    """
    def __init__(self, tr_id, pn):
        self.id = tr_id
        self.pn = pn
        self.input = {}
        self.output = {}
        self.pl_linked = []

    def __str__(self):
        """ Transition to .net format.
        """
        text = "tr {}  ".format(self.id)
        for src, weight in self.input.items():
            text += self.str_arc(src, weight)
        text += '-> '
        for dest, weight in self.output.items():
            text += self.str_arc(dest, weight)
        text += '\n'
        return text

    def str_arc(self, pl, weight):
        """ Arc to .net format.
        """
        text = ""
        text += pl.id
        if weight > 1:
            text += '*' + str(weight)
        if weight < 0:
            text += '?-' + str(- weight)
        text += ' '
        return text

    def smtlib(self, k):
        """ Transition relation from places at order k to order k + 1.
            Textbook version not used.
            SMT-LIB format
        """
        smt_input = "\t(and\n\t\t"
        for pl, weight in self.input.items():
            if weight > 0:
                smt_input += "(>= {}@{} {})".format(pl.id, k, weight)
            else:
                smt_input += "(< {}@{} {})".format(pl.id, k, - weight)
        smt_input += "\n\t\t"
        for pl, weight in self.input.items():
            if weight > 0:
                if pl in self.output:
                    smt_input += "(= {}@{} (- (+ {}@{} {}) {}))".format(pl.id, k + 1, pl.id, k, self.output[pl], weight)
                else:
                    smt_input += "(= {}@{} (- {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        for pl, weight in self.output.items():
            if pl not in self.input or self.input[pl] < 0:
                smt_input += "(= {}@{} (+ {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        smt_input += "\n\t\t"
        for pl in self.pn.places.values():
            if pl not in self.pl_linked:
                smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        smt_input += "\n\t)\n"
        return smt_input

    def smtlib_textbook(self, k):
        """ Transition relation from places at order k to order k + 1.
            Textbook version not used.
            SMT-LIB format
        """
        smt_input = "\t(and\n\t\t(=>\n\t\t\t(and "
        for pl, weight in self.input.items():
            if weight > 0:
                smt_input += "(>= {}@{} {})".format(pl.id, k, weight)
            else:
                smt_input += "(< {}@{} {})".format(pl.id, k, - weight)
        smt_input += ")\n\t\t\t(and "
        for pl, weight in self.input.items():
            if weight > 0:
                if pl in self.output:
                    smt_input += "(= {}@{} (- (+ {}@{} {}) {}))".format(pl.id, k + 1, pl.id, k, self.output[pl], weight)
                else:
                    smt_input += "(= {}@{} (- {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        for pl, weight in self.output.items():
            if pl not in self.input or self.input[pl] < 0:
                smt_input += "(= {}@{} (+ {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        for pl in self.pn.places.values():
            if pl not in self.pl_linked:
                smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        smt_input += ")\n\t\t)\n\t\t(=>\n\t\t\t(or "
        for pl, weight in self.input.items():
            if weight > 0:
                smt_input += "(< {}@{} {})".format(pl.id, k, weight)
            else:
                smt_input += "(>= {}@{} {})".format(pl.id, k, - weight)
        smt_input += ")\n\t\t\t(and "
        for pl in self.pn.places.values():
            smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        smt_input += ")\n\t\t)\n\t)\n"
        return smt_input


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
