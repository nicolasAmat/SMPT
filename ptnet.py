#!/usr/bin/env python3

"""
Petri Net Module

Input file format: .net
Standard: http://projects.laas.fr/tina//manuals/formats.html

This file is part of SMPT.

SMPT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

SMPT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with SMPT. If not, see <https://www.gnu.org/licenses/>.
"""

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "3.0.0"

import re
import sys
import xml.etree.ElementTree as ET


class PetriNet:
    """
    Petri net defined by:
    - an identifier,
    - a finite set of places (identified by names),
    - a finite set of transitions (identified by names).
    """

    def __init__(self, filename, pnml_filename=None):
        """ Initializer.
        """
        self.id = ""

        self.places = {}
        self.transitions = {}

        self.pnml_mapping = False
        self.places_mapping = {}
        self.transitions_mapping = {}
        if pnml_filename is not None:
            self.pnml_mapping = True
            self.ids_mapping(pnml_filename)

        self.parse_net(filename)

    def __str__(self):
        """ Petri net to .net format.
        """
        text = "net {}\n".format(self.id)
        text += ''.join(map(str, self.places.values()))
        text += ''.join(map(str, self.transitions.values()))

        return text

    def smtlib_declare_places(self, k=None):
        """ Declare places.
            SMT-LIB format
        """
        return ''.join(map(lambda pl: pl.smtlib_declare(k), self.places.values()))

    def minizinc_declare_places(self):
        """ Declare places.
            MiniZinc format
        """
        return ''.join(map(lambda pl: pl.minizinc_declare(), self.places.values()))

    def smtlib_initial_marking(self, k=None):
        """ Assert the initial marking.
            SMT-LIB format
        """
        return ''.join(map(lambda pl: pl.smtlib_initial_marking(k), self.places.values()))

    def smtlib_transition_relation(self, k, eq=False):
        """ Transition relation from places at order k to order k + 1.
            SMT-LIB format
        """
        if not self.places:
            return ""

        smt_input = "(assert (or \n"
        smt_input += ''.join(map(lambda tr: tr.smtlib(k), self.transitions.values()))
        if eq:
            smt_input += "\t(and\n\t\t"
            smt_input += ''.join(map(lambda pl: "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k), self.places.values()))
            smt_input += "\n\t)"
        smt_input += "\n))\n"

        return smt_input

    def smtlib_transition_relation_textbook(self, k):
        """ Transition relations from places at order k to order k + 1.
            Textbook version not used.
            SMT-LIB format
        """
        if not self.places:
            return ""

        smt_input = "(assert (or \n"
        smt_input += ''.join(map(lambda tr: tr.smtlib_textbook(k), self.transitions.values()))
        smt_input += "))\n"

        return smt_input

    def ids_mapping(self, pnml_filename):
        """ Map `names` to `ids` from the PNML file.
        """
        xmlns = "{http://www.pnml.org/version-2009/grammar/pnml}"

        tree = ET.parse(pnml_filename)
        root = tree.getroot()

        for place_node in root.iter(xmlns + 'place'):
            place_id = place_node.attrib['id']
            place_name = place_node.find(xmlns + 'name/' + xmlns + 'text').text
            self.places_mapping[place_id] = place_name

        for transition_node in root.iter(xmlns + 'transition'):
            transition_id = transition_node.attrib['id']
            transition_name = transition_node.find(xmlns + 'name/' + xmlns + 'text').text
            self.transitions_mapping[transition_id] = transition_name

    def parse_net(self, filename):
        """ Petri net parser.
            Input format: .net
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = re.split(r'\s+', line.strip().replace('#', '.'))  # '#' forbidden in SMT-LIB
                    element = content.pop(0)
                    if element == "net":
                        self.id = content[0].replace('{', '').replace('}', '')
                    if element == "tr":
                        self.parse_transition(content)
                    if element == "pl":
                        self.parse_place(content)
            fp.close()
        except FileNotFoundError as e:
            sys.exit(e)

    def parse_transition(self, content):
        """ Transition parser.
            Input format: .net
        """
        transition_id = content.pop(0).replace('{', '').replace('}', '')  # '{' and '}' forbidden in SMT-LIB

        if transition_id in self.transitions:
            tr = self.transitions[transition_id]
        else:
            tr = Transition(transition_id, self)
            self.transitions[transition_id] = tr

        content = self.parse_label(content)

        arrow = content.index("->")
        inputs = content[0:arrow]
        outputs = content[arrow + 1:]

        for arc in inputs:
            tr.connected_places.append(self.parse_arc(arc, tr.inputs, tr.outputs))

        for arc in outputs:
            tr.connected_places.append(self.parse_arc(arc, tr.outputs))

        tr.normalize_test_arcs()
        tr.compute_pre_vector()

    def parse_arc(self, arc, arcs, opposite_arcs=[]):
        """ Arc parser.
            Can handle:
                - Normal Arc,
                - Test Arc,
                - Inhibitor Arc.
            Input format: .net
        """
        arc = arc.replace('{', '').replace('}', '')  # '{' and '}' forbidden in SMT-LIB

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
            new_place = Place(place_id)
            self.places[place_id] = new_place

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
        place_id = content.pop(0).replace('{', '').replace('}', '')  # '{' and '}' forbidden in SMT-LIB

        content = self.parse_label(content)

        if content:
            initial_marking = int(content[0].replace('(', '').replace(')', ''))
        else:
            initial_marking = 0

        if place_id not in self.places:
            new_place = Place(place_id, initial_marking)
            self.places[place_id] = new_place
        else:
            self.places.get(place_id).initial_marking = initial_marking

    def parse_label(self, content):
        """ Label parser.
            Input format: .net
        """
        index = 0
        if content and content[index] == ':':
            label_skipped = content[index + 1][0] != '{'
            index = 2
            while not label_skipped:
                label_skipped = content[index][-1] == '}'
                index += 1
        return content[index:]

    def get_transition_from_step(self, m_1, m_2):
        """ Return an associate transition to a step m_1 -> m_2.
        """
        # Get inputs and outputs
        inputs, outputs = {}, {}
        for place in self.places.values():
            # Inputs
            if m_1[place] > m_2[place]:
                inputs[place] = m_1[place] - m_2[place]
            # Outpus
            if m_1[place] < m_2[place]:
                outputs[place] = m_2[place] - m_1[place]

        # Return the corresponding transition
        for transition in self.transitions.values():
            if transition.inputs == inputs and transition.outputs == outputs and all(m_1[place] >= pre for place, pre in transition.pre.items()):
                return transition

        return None


class Place:
    """
    Place defined by:
    - an identifier,
    - an initial marking,
    """

    def __init__(self, place_id, initial_marking=0):
        """ Initializer.
        """
        self.id = place_id
        self.initial_marking = initial_marking

    def __str__(self):
        """ Place to .net format.
        """
        if self.initial_marking:
            return "pl {} ({})\n".format(self.id, self.initial_marking)
        else:
            return ""

    def smtlib_declare(self, k=None):
        """ Declare a place.
            SMT-LIB format
        """
        if k is not None:
            return "(declare-const {}@{} Int)\n(assert (>= {}@{} 0))\n".format(self.id, k, self.id, k)
        else:
            return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.id, self.id)

    def minizinc_declare(self):
        """ Declare a place.
            MiniZinc format
        """
        return "var 0..MAX: {};\n".format(self.id)

    def smtlib_initial_marking(self, k=None):
        """ Assertions to set the initial marking.
            SMT-LIB format
        """
        if k is not None:
            return "(assert (= {}@{} {}))\n".format(self.id, k, self.initial_marking)
        else:
            return "(assert (= {} {}))\n".format(self.id, self.initial_marking)


class Transition:
    """
    Transition defined by:
    - an identifier
    - input places (flow)
      associated to the weight of the arc,
    - output places (flow)
      associated to the weight of the arc,
    - test places (null flow),
      associated to the weight of the arc,
    - pre vector (firing condition),
    - a list of the places connected to the transition.
    """

    def __init__(self, transition_id, ptnet):
        """ Initializer.
        """
        self.id = transition_id

        self.inputs = {}
        self.outputs = {}
        self.tests = {}
        self.pre = {}

        self.connected_places = []
        self.ptnet = ptnet

    def __str__(self):
        """ Transition to .net format.
        """
        text = "tr {} ".format(self.id)

        for src, weight in self.pre.items():
            text += ' ' + self.str_arc(src, weight)

        text += ' ->'

        for dest, weight in self.outputs.items():
            if dest not in self.tests:
                text += ' ' + self.str_arc(dest, weight)

        for dest, weight in self.tests.items():
            if dest in self.outputs:
                weight += self.outputs[dest]
            text += ' ' + self.str_arc(dest, weight)

        text += '\n'
        return text

    def str_arc(self, place, weight):
        """ Arc to .net format.
        """
        text = place.id

        if weight > 1:
            text += '*' + str(weight)

        if weight < 0:
            text += '?-' + str(-weight)

        return text

    def smtlib(self, k):
        """ Transition relation from places at order k to order k + 1.
            SMT-LIB format
        """
        smt_input = "\t(and\n\t\t"

        # Firing condition on input places
        for pl, weight in self.pre.items():
            if weight > 0:
                smt_input += "(>= {}@{} {})".format(pl.id, k, weight)
            else:
                smt_input += "(< {}@{} {})".format(pl.id, k, -weight)
        smt_input += "\n\t\t"

        # Update input places
        for pl, weight in self.inputs.items():
            if weight > 0:
                if pl in self.outputs:
                    smt_input += "(= {}@{} (- (+ {}@{} {}) {}))".format(pl.id, k + 1, pl.id, k, self.outputs[pl],
                                                                        weight)
                else:
                    smt_input += "(= {}@{} (- {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)

        # Update output places
        for pl, weight in self.outputs.items():
            if pl not in self.inputs or self.inputs[pl] < 0:
                smt_input += "(= {}@{} (+ {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)
        smt_input += "\n\t\t"

        # Unconnected places must not be changed
        for pl in self.ptnet.places.values():
            if pl not in self.connected_places or (pl in self.tests and pl not in self.inputs and pl not in self.outputs):
                smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)

        smt_input += "\n\t)\n"

        return smt_input

    def smtlib_textbook(self, k):
        """ Transition relation from places at order k to order k + 1.
            Textbook version (not used).
            SMT-LIB format
        """
        smt_input = "\t(and\n\t\t(=>\n\t\t\t(and "

        # Firing condition on input places
        for pl, weight in self.pre.items():
            if weight > 0:
                smt_input += "(>= {}@{} {})".format(pl.id, k, weight)
            else:
                smt_input += "(< {}@{} {})".format(pl.id, k, -weight)
        smt_input += ")\n\t\t\t(and "

        # Update input places
        for pl, weight in self.inputs.items():
            if weight > 0:
                if pl in self.outputs:
                    smt_input += "(= {}@{} (- (+ {}@{} {}) {}))".format(pl.id, k + 1, pl.id, k, self.outputs[pl],
                                                                        weight)
                else:
                    smt_input += "(= {}@{} (- {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)

        # Update output places
        for pl, weight in self.outputs.items():
            if pl not in self.inputs or self.inputs[pl] < 0:
                smt_input += "(= {}@{} (+ {}@{} {}))".format(pl.id, k + 1, pl.id, k, weight)

        # Unconnected places must not be changed
        for pl in self.ptnet.places.values():
            if pl not in self.connected_places or (pl in self.tests and pl not in self.inputs and pl not in self.outputs):
                smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        smt_input += ")\n\t\t)\n\t\t(=>\n\t\t\t(or "

        # Dead condition on input places
        for pl, weight in self.pre.items():
            if weight > 0:
                smt_input += "(< {}@{} {})".format(pl.id, k, weight)
            else:
                smt_input += "(>= {}@{} {})".format(pl.id, k, -weight)
        smt_input += ")\n\t\t\t(and "

        # Places must not change
        for pl in self.ptnet.places.values():
            smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)
        smt_input += ")\n\t\t)\n\t)\n"

        return smt_input

    def normalize_test_arcs(self):
        """ Normalize test arcs.
            If pre(t,p) > 0 and post(t,p) > 0 then
            - test(t,p) = |pre(t,p) - post(t,p)|,
            - input(t,p) = max(0, pre(t,p) - |pre(t,p) - post(t,p)|),
            - output(t,p) = max(0, post(t,p) - |pre(t,p) - post(t,p)|).
        """
        for place in set(self.inputs.keys()) & set(self.outputs.keys()):
            
            if self.inputs[place] == self.outputs[place]:
                self.tests[place] = self.inputs[place]
                del self.inputs[place]
                del self.outputs[place]

            elif self.inputs[place] > self.outputs[place]:
                self.tests[place] = self.outputs[place]
                self.inputs[place] = self.inputs[place] - self.outputs[place]
                del self.outputs[place]

            elif self.inputs[place] < self.outputs[place]:
                self.outputs[place] = self.outputs[place] - self.inputs[place]
                self.tests[place] = self.inputs[place]
                del self.inputs[place]

    def compute_pre_vector(self):
        """ Compute pre(t).
        """
        for place, weight in self.inputs.items():
            if place in self.tests:
                weight += self.tests
            self.pre[place] = weight

        for place, weight in self.tests.items():
            if place not in self.inputs:
                self.pre[place] = weight


class Marking:
    """ TODO: to implement 
    """
    def __init__(self):
        pass

    def __str__(self):
        return ""


if __name__ == "__main__":

    if len(sys.argv) == 1:
        sys.exit("Argument missing: ./ptnet.py <path_to_Petri_net>")

    ptnet = PetriNet(sys.argv[1])

    print("> Petri Net (.net format)")
    print("-------------------------")
    print(ptnet)

    print("> Generated SMT-LIB")
    print("-------------------")
    print(">> Declare places")
    print(ptnet.smtlib_declare_places())
    print(">> Initial marking")
    print(ptnet.smtlib_initial_marking())
    print(">> Transition relation (0 -> 1)")
    print(ptnet.smtlib_transition_relation(0))
