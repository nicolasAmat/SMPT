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

from __future__ import annotations

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import re
import sys
import xml.etree.ElementTree as ET
from typing import Optional


MULTIPLIER_TO_INT = {
    'K': 1000,
    'M': 1000000,
    'G': 1000000000,
    'T': 1000000000000,
    'P': 1000000000000000,
    'E': 1000000000000000000
}


class PetriNet:
    """ Petri net.

    Attributes
    ----------
    id : str
        Identifier.
    filename : str
        Petri net filename.
    places : dict of str: Place
        Finite set of places (identified by names).
    transitions : dict of str: Transition
        Finite set of transitions (identified by names).
    initial_marking : Marking
        Initial marking.
    skeleton : bool
        Skeleton flag.
    colored : bool
        Colored flag.
    colored_places_mapping : dict of str: list of str
        Correspondence of the colored places with the unfolded ones (not colored).
    colored_transitions_mapping: dict of str: list of str
        Correspondence of the colored transitions with the unfolded ones (not colored).
    state_equation : bool
        State equation method flag.
    parikh: bool, optional
        Parikh computation flag.
    pnml_mapping : bool
        PNML mapping flag.
    pnml_places_mapping : dict of str: str
        Correspondence of the place ids with the names (.pnml).
    pnml_transitions_mapping: dict of str: str
        Correspondence of the transition ids with the names (.pnml).
    nupn : NUPN, optional
        NUPN flag.
    """

    def __init__(self, filename: str, pnml_filename: str = None, skeleton: bool = False, colored: bool = False, state_equation: bool = False, parikh: bool = False) -> None:
        """ Initializer.

        Parameters
        ----------
        filename : str
            Petri net filename.
        pnml_filename : str, optional
            PNML filename (.pnml format).
        skeleton: : bool, optional
            Skeleton flag.
        colored: : bool, optional
            Colored flag.
        state_equation : bool, optional
            State equation method flag.
        parikh : bool, optional
            Parikh computation flag.
        """
        self.id: str = ""
        self.filename: str = filename

        self.places: dict[str, Place] = {}
        self.transitions: dict[str, Transition] = {}
        self.initial_marking: Marking = Marking()

        # Colored and skeleton management
        self.skeleton: bool = skeleton
        self.colored: bool = colored

        # Mapping when colored
        self.colored_places_mapping: dict[str, list[str]] = {}
        self.colored_transitions_mapping: dict[str, list[str]] = {}

        # State equation management
        self.state_equation: bool = state_equation

        # Parikh computation flag
        self.parikh: bool = parikh

        # `.pnml` management
        self.pnml_mapping: bool = False

        # Mapping with `.pnml`
        self.pnml_places_mapping: dict[str, str] = {}
        self.pnml_transitions_mapping: dict[str, str] = {}

        if pnml_filename is not None:
            self.pnml_mapping = True
            self.ids_mapping(pnml_filename)

        # NUPN management
        self.nupn: Optional[NUPN] = None
        if pnml_filename is not None:
            self.nupn = NUPN(pnml_filename)

        # Parse the `.net` file
        self.parse_net(filename)

    def __str__(self) -> str:
        """ Petri net to .net format.

        Returns
        -------
        str
            .net format.
        """
        text = "net {}\n".format(self.id)
        text += ''.join(map(str, self.places.values()))
        text += ''.join(map(str, self.transitions.values()))

        return text

    def smtlib_declare_places(self, k: Optional[int] = None) -> str:
        """ Declare places.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda pl: pl.smtlib_declare(k), self.places.values()))

    def minizinc_declare_places(self) -> str:
        """ Declare places.

        Returns
        -------
        str
            MiniZinc format.
        """
        return ''.join(map(lambda pl: pl.minizinc_declare(), self.places.values()))

    def smtlib_declare_transitions(self, parikh: bool = False) -> str:
        """ Declare transitions.
        
        Parameters
        ----------
        parikh : bool, optional
            Computation of parikh vector enabled.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda tr: tr.smtlib_declare(parikh), self.transitions.values()))

    def smtlib_initial_marking(self, k: Optional[int] = None) -> str:
        """ Assert the initial marking.
        
        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return self.initial_marking.smtlib(k)

    def smtlib_transition_relation(self, k: int, eq: bool = True, tr: bool = False) -> str:
        """ Transition relation from places at order k to order k + 1.
        
        Parameters
        ----------
        k : int
            Order.
        eq : bool, optional
            Add EQ(p_k, p_{k+1}) predicate in the transition relation.
        tr : bool, optional
            Add transition ids.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        if not self.places:
            return smt_input

        if tr:
            smt_input += "(declare-const TRACE@{} Int)\n".format(k)

        smt_input += "(assert (or \n"

        if tr:
            smt_input += ''.join(map(lambda it: it[1].smtlib(k, id=it[0]),
                                 enumerate(self.transitions.values())))
        else:
            smt_input += ''.join(map(lambda tr: tr.smtlib(k),
                                     self.transitions.values()))
        if eq:
            smt_input += "\t(and\n\t\t"
            if tr:
                smt_input += "(= TRACE@{} (-1))\n\t\t".format(k)
            smt_input += ''.join(map(lambda pl: "(= {}@{} {}@{})".format(
                pl.id, k + 1, pl.id, k), self.places.values()))
            smt_input += "\n\t)"
        smt_input += "\n))\n"

        return smt_input

    def smtlib_state_equation(self, k: Optional[int] = None, parikh: bool = False) -> str:
        """ Assert the state equation (potentially reachable markings).

        Parameters
        ----------
        k : int, optional
            Order.
        
        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda pl: pl.smtlib_state_equation(k, parikh), self.places.values()))

    def smtlib_read_arc_constraints(self, parikh: bool = False) -> str:
        """ Assert read arc constraints.

        Parameters
        ----------
        parikh : bool, optional
            Computation of parikh vector enabled.

        Returns
        -------
            SMTT-LIB format.
        """
        return ''.join(map(lambda tr: tr.smtlib_read_arc_constraints(parikh), self.transitions.values()))

    def smtlib_declare_trap(self) -> str:
        """ Declare trap Boolean variable for each place.
            
        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda pl: pl.smtlib_declare_trap(), self.places.values()))

    def smtlib_trap_initially_marked(self) -> str:
        """ Assert that places in the trap must be initially marked.
            
        Returns
        -------
        str
            SMT-LIB format.
        """
        return self.initial_marking.smtlib_trap_initially_marked()

    def smtlib_trap_definition(self) -> str:
        """ Assert trap definition for each place.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda pl: pl.smtlib_trap_definition(), self.places.values()))

    def smtlib_transition_relation_textbook(self, k: int) -> str:
        """ Transition relations from places at order k to order k + 1.

        Note
        ----
        Textbook version not used.
        
        Returns
        -------
        str
            SMT-LIB format.
        """
        if not self.places:
            return ""

        smt_input = "(assert (or \n"
        smt_input += ''.join(map(lambda tr: tr.smtlib_textbook(k),
                             self.transitions.values()))
        smt_input += "))\n"

        return smt_input

    def ids_mapping(self, filename: str) -> None:
        """ Map `names` to `ids` from the PNML file.

        Parameters
        ----------
        filename : str
            PNML filename (.pnml format).
        """
        xmlns = "{http://www.pnml.org/version-2009/grammar/pnml}"

        tree = ET.parse(filename)
        root = tree.getroot()

        for place_node in root.iter(xmlns + 'place'):
            place_id = place_node.attrib['id']
            place_name = place_node.find(xmlns + 'name/' + xmlns + 'text').text.replace(
                '#', '.').replace(',', '.')  # '#' and ',' forbidden in SMT-LIB
            self.pnml_places_mapping[place_id] = place_name

        for transition_node in root.iter(xmlns + 'transition'):
            transition_id = transition_node.attrib['id']
            transition_name = transition_node.find(xmlns + 'name/' + xmlns + 'text').text.replace(
                '#', '.').replace(',', '.')  # '#' and ',' forbidden in SMT-LIB
            self.pnml_transitions_mapping[transition_id] = transition_name

    def parse_net(self, filename: str) -> None:
        """ Petri net parser.

        Parameters
        ----------
        filename : str
            Petri net filename (.net format).

        Raises
        ------
        FileNotFoundError
            Petri net file not found.
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():

                    # '#' and ',' forbidden in SMT-LIB
                    content = re.split(
                        r'\s+', line.strip().replace('#', '.').replace(',', '.'))

                    # Skip empty lines and get the first identifier
                    if not content:
                        continue
                    else:
                        element = content.pop(0)

                    # Colored Petri net
                    if element == '.':
                        kind_mapping = content.pop(0)
                        if kind_mapping == 'pl':
                            colored_place = content.pop(0)
                            self.colored_places_mapping[colored_place] = content
                        if kind_mapping == 'tr':
                            colored_transition = content.pop(0)
                            self.colored_transitions_mapping[colored_transition] = content

                    # Net id
                    if element == "net":
                        self.id = content[0].replace('{', '').replace('}', '')

                    # Transition arcs
                    if element == "tr":
                        self.parse_transition(content)

                    # Place
                    if element == "pl":
                        self.parse_place(content)
            fp.close()
        except FileNotFoundError as e:
            sys.exit(e)

    def parse_transition(self, content: list[str]) -> None:
        """ Transition parser.

        Parameters
        ----------
        content : list of string
            Content to parse (.net format).
        """
        transition_id = content.pop(0).replace(
            '{', '').replace('}', '')  # '{' and '}' forbidden in SMT-LIB

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
            tr.connected_places.append(self.parse_arc(arc, tr.pre, tr.post))

        for arc in outputs:
            tr.connected_places.append(self.parse_arc(arc, tr.post))

        tr.normalize_flows(self.state_equation)

    def parse_arc(self, content: str, arcs: dict[Place, int], opposite_arcs: dict[Place, int] = None) -> Place:
        """ Arc parser.
    
        Note
        ----
        Can handle:
            - Normal Arc,
            - Test Arc,
            - Inhibitor Arc.

        Parameters
        ----------
        content : 
            Content to parse (.net format).
        arcs : dict of Place: int
            Current arcs.
        opposite_arcs : dict of Place: int, optional
            Opposite arcs.

        Returns
        -------

        """
        content = content.replace('{', '').replace(
            '}', '')  # '{' and '}' forbidden in SMT-LIB

        test_arc = False

        if '?-' in content:
            place_id, _, weight_str = content.partition('?-')
            # To recognize an inhibitor arc, we set a negative weight
            weight = - self.parse_value(weight_str)
        elif '?' in content:
            test_arc = True
            place_id, _, weight_str = content.partition('?')
            weight = self.parse_value(weight_str)
        elif '*' in content:
            place_id, _, weight_str = content.partition('*')
            weight = self.parse_value(weight_str)
        else:
            place_id = content
            weight = 1

        if place_id not in self.places:
            new_place = Place(place_id)
            self.places[place_id] = new_place
            self.initial_marking.tokens[new_place] = 0

        pl = self.places.get(place_id)
        arcs[pl] = weight

        # In a case of a test arc, we add a second arc
        if test_arc and opposite_arcs is not None:
            opposite_arcs[pl] = weight

        return pl

    def parse_place(self, content: list[str]) -> None:
        """ Place parser.

        Parameters
        ----------
        content : list of str
            Place to parse (.net format).
        """
        place_id = content.pop(0).replace('{', '').replace(
            '}', '')  # '{' and '}' forbidden in SMT-LIB

        content = self.parse_label(content)

        if content:
            initial_marking = self.parse_value(
                content[0].replace('(', '').replace(')', ''))
        else:
            initial_marking = 0

        if place_id not in self.places:
            place = Place(place_id, initial_marking)
            self.places[place_id] = place
        else:
            place = self.places.get(place_id)
            place.initial_marking = initial_marking

        self.initial_marking.tokens[place] = initial_marking

    def parse_label(self, content: list[str]) -> list[str]:
        """ Label parser.

        Parameters
        ----------
        content : list of str
            Content to parse (.net format).

        Returns
        -------
        list of str
            Content without labels.

        """
        index = 0
        if content and content[index] == ':':
            label_skipped = content[index + 1][0] != '{'
            index = 2
            while not label_skipped:
                label_skipped = content[index][-1] == '}'
                index += 1
        return content[index:]

    def parse_value(self, content: str) -> int:
        """ Parse integer value.

        Parameters
        ----------
        content : str
            Content to parse (.net format).

        Returns
        -------
        int
            Corresponding integer value.

        Raises
        ------
        ValueError
            Incorrect integer value.

        """
        if content.isnumeric():
            return int(content)

        multiplier = content[-1]

        if multiplier not in MULTIPLIER_TO_INT:
            raise ValueError("Incorrect integer value")

        return int(content[:-1]) * MULTIPLIER_TO_INT[multiplier]

    def get_transition_from_step(self, m_1: Marking, m_2: Marking) -> Optional[Transition]:
        """ Return an associate transition to a step m_1 -> m_2.

        Parameters
        ----------
        m_1 : Marking
            Starting marking.
        m_2 : Marking
            Reached marking.

        Returns
        -------
        Transitions, optional
            Transition corresponding to the step.
        """
        # Get inputs and outputs
        inputs, outputs = {}, {}
        for place in self.places.values():
            # Inputs
            if m_1.tokens[place] > m_2.tokens[place]:
                inputs[place] = m_1.tokens[place] - m_2.tokens[place]
            # Outputs
            if m_1.tokens[place] < m_2.tokens[place]:
                outputs[place] = m_2.tokens[place] - m_1.tokens[place]

        # Return the corresponding transition
        for transition in self.transitions.values():
            if transition.inputs == inputs and transition.outputs == outputs and all(m_1.tokens[place] >= pre for place, pre in transition.pre.items()):
                return transition

        return None


class Place:
    """ Place.

    Attributes
    ----------
    id : str
        An identifier.
    initial_marking : Marking
        Initial marking of the place.
    delta : dict of Transition: int
        Delta vector.
    input_transitions: set of Transition
        Input transitions.
    output_transitions : set of Transition 
        Output transitions.
    """

    def __init__(self, place_id: str, initial_marking: int = 0) -> None:
        """ Initializer.

        Parameters
        ----------
        place_id : str
            An identifier.
        initial_marking : int, optional
            Initial marking of the place.
        """
        self.id: str = place_id
        self.initial_marking: int = initial_marking

        # Optional (used for state equation)
        self.delta: dict[Transition, int] = {}
        self.input_transitions: set[Transition] = set()
        self.output_transitions: set[Transition] = set()

    def __str__(self) -> str:
        """ Place to .net format.

        Returns
        -------
        str
            .net format.
        """
        if self.initial_marking:
            return "pl {} ({})\n".format(self.id, self.initial_marking)
        else:
            return ""

    def smtlib(self, k: Optional[int] = None) -> str:
        """ Place identifier.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "{}@{}".format(self.id, k) if k is not None else self.id

    def smtlib_declare(self, k: Optional[int] = None) -> str:
        """ Declare a place.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.smtlib(k), self.smtlib(k))

    def minizinc_declare(self) -> str:
        """ Declare a place.

        Returns
        -------
        str
            MiniZinc format.
        """
        return "var 0..MAX: {};\n".format(self.id)

    def smtlib_initial_marking(self, k: Optional[int] = None) -> str:
        """ Assert the initial marking.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "(assert (= {} {}))\n".format(self.smtlib(k), self.initial_marking)

    def smtlib_state_equation(self, k: Optional[int] = None, parikh: bool = False) -> str:
        """ Assert the state equation.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ' '.join(["(* {} {})".format(tr.id + "@t" if parikh else tr.id, weight) if weight !=
                             1 else tr.id + "@t" if parikh else tr.id for tr, weight in self.delta.items()])

        if self.initial_marking != 0:
            smt_input += " " + str(self.initial_marking)

        if self.initial_marking != 0 or len(self.delta) > 1:
            smt_input = "(+ {})".format(smt_input)

        if not smt_input:
            smt_input = "0"

        return "(assert (= {} {}))\n".format(self.smtlib(k), smt_input)

    def smtlib_declare_trap(self) -> str:
        """ Declare trap Boolean variable.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "(declare-const {} Bool)\n".format(self.id)

    def smtlib_trap_definition(self) -> str:
        """ Assert trap definition for each place.

        Returns
        -------
        str
            SMT-LIB format.
        """
        if not self.output_transitions:
            return ""

        smt_input = ' '.join(
            map(lambda tr: tr.smtlib_trap_definition_helper(), self.output_transitions))

        if len(self.output_transitions) > 1:
            smt_input = "(and {})".format(smt_input)

        return "(assert (=> {} {}))\n".format(self.id, smt_input)


class Transition:
    """ Transition.

    Attributes
    ----------
    id : str
        An identifier.
    inputs : dict of Place: int
        Input places (flow), associated to the weight of the arc.
    outputs : dict of Place: int
        Output places (flow), associated to the weight of the arc.
    test: dict of Place: int
        Test places (null flow), associated to the weight of the arc.
    pre: dict of Place: int
        Pre vector (firing condition).
    post: dict of Place: int
        Post vector.
    delta: dict of Place: int
        Delta vector (change marking).
    connected_places: list of Place
        List of the places connected to the transition.
    ptnet: PetriNet
        Associated Petri net.
    """

    def __init__(self, transition_id: str, ptnet: PetriNet) -> None:
        """ Initializer.

        Parameters
        ----------
        transition_id : str
            An identifier.
        ptnet : PetriNet
            Associated Petri net.
        """
        self.id: str = transition_id

        self.inputs: dict[Place, int] = {}
        self.outputs: dict[Place, int] = {}
        self.tests: dict[Place, int] = {}

        self.pre: dict[Place, int] = {}
        self.post: dict[Place, int] = {}
        self.delta: dict[Place, int] = {}

        self.connected_places: list[Place] = []
        self.ptnet: PetriNet = ptnet

    def __str__(self) -> str:
        """ Transition to textual format.
        
        Returns
        -------
        str
            .net format.
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

    def str_arc(self, place: Place, weight: int) -> str:
        """ Arc to textual format.

        Parameters
        ----------
        place : place
            Input place.
        weight : int
            Weight of the arc (negative if inhibitor).

        Returns
        -------
        str
            .net format.
        """
        text = place.id

        if weight > 1:
            text += '*' + str(weight)

        if weight < 0:
            text += '?-' + str(-weight)

        return text

    def smtlib(self, k: int, id: Optional[int] = None) -> str:
        """ Transition relation from places at order k to order k + 1.
            
        Parameters
        ----------
        k : int
            Order.
        id : int, optional
            Id of the transition.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = "\t(and\n\t\t"

        # Trace label
        if id is not None:
            smt_input += "(= TRACE@{} {})\n\t\t".format(k, id)

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
                    smt_input += "(= {}@{} (- {}@{} {}))".format(pl.id,
                                                                 k + 1, pl.id, k, weight)

        # Update output places
        for pl, weight in self.outputs.items():
            if pl not in self.inputs or self.inputs[pl] < 0:
                smt_input += "(= {}@{} (+ {}@{} {}))".format(pl.id,
                                                             k + 1, pl.id, k, weight)
        smt_input += "\n\t\t"

        # Unconnected places must not be changed
        for pl in self.ptnet.places.values():
            if pl not in self.connected_places or (pl in self.tests and pl not in self.inputs and pl not in self.outputs):
                smt_input += "(= {}@{} {}@{})".format(pl.id, k + 1, pl.id, k)

        smt_input += "\n\t)\n"

        return smt_input

    def smtlib_textbook(self, k: int) -> str:
        """ Transition relation from places at order k to order k + 1.
        
        Note
        ----
        Textbook version, not used in practice.
        
        Parameters
        ----------
        k : int
            Order.

        Returns
        -------
        str
            SMT-LIB format.
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
                    smt_input += "(= {}@{} (- {}@{} {}))".format(pl.id,
                                                                 k + 1, pl.id, k, weight)

        # Update output places
        for pl, weight in self.outputs.items():
            if pl not in self.inputs or self.inputs[pl] < 0:
                smt_input += "(= {}@{} (+ {}@{} {}))".format(pl.id,
                                                             k + 1, pl.id, k, weight)

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

    def smtlib_declare(self, parikh: bool = False) -> str:
        """ Declare a transition.

        Parameters
        ----------
        parikh : bool, optional
            Computation of parikh vector enabled.

        Returns
        -------
        str
            SMT-LIB format.
        """
        identifier = self.id + "@t" if parikh else self.id
        return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(identifier, identifier)

    def smtlib_read_arc_constraints(self, parikh : bool = False) -> str:
        """ Assert read arc constraints.

        Parameters
        ----------
        parikh : bool, optional
            Computation of parikh vector enabled.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        # for p s.t. pre(t,p) > 0
        for pl, weight in self.pre.items():
            # if delta(t,p) = 0 and pre(t,p) > m0(p)
            if not self.delta.get(pl, 0) and weight > pl.initial_marking:
                # t > 0 => \/_{t' s.t. post(t,p) > 0 \ t and delta(t',p) > 0} t' > 0
                right_member = ["(> {} 0)".format(
                    tr.id + "@t" if parikh else tr.id) for tr in pl.input_transitions if tr != self and tr.delta.get(pl, 0) > 0]
                if not right_member:
                    smt_input_right_member = "false"
                elif len(right_member) == 1:
                    smt_input_right_member = ''.join(right_member)
                else:
                    smt_input_right_member = "(or {})".format(
                        ''.join(right_member))
                smt_input += "(assert (=> (> {} 0) {}))\n".format(self.id + "@t" if parikh else self.id,
                                                                  smt_input_right_member)

        return smt_input

    def smtlib_trap_definition_helper(self) -> str:
        """ Helper to assert trap definition for each place.

        Returns
        -------
        str
            SMT-LIB format.
        """
        # \/_{p' s.t. post(t, p') > 0} p'

        if not self.post:
            return "false"

        smt_input = ' '.join(map(lambda pl: pl.id, self.post))

        if len(self.post) > 1:
            smt_input = "(or {})".format(smt_input)

        return smt_input

    def normalize_flows(self, state_equation: bool = False) -> None:
        """ Normalize arcs.

        Note
        ----
        If pre(t,p) > 0 and post(t,p) > 0 then
        - delta(t,p) = abs(pre(t,p) - post(t,p))
        - tests(t,p) = min(pre(t,p), post(t,p))
        - inputs(t,p) = max(0, pre(t,p) - delta(t,p))
        - outputs(t,p) = max(0, post(t,p) - delta(t,p))
        Else if pre(t, p) > 0 then
        - inputs(t,p) = pre(t,p)
        - delta(t,p) = -pre(t,p)
        Else if post(t,p) > 0 then
        - output(t,p) = post(t,p)
        - delta(t,p) = post(t,p)

        Parameters
        ----------
        state_equation : bool, optional
            State equation method flag.
        """
        for place in set(self.pre.keys()) | set(self.post.keys()):

            if place in self.pre and place in self.post:
                if self.pre[place] == self.post[place]:
                    self.tests[place] = self.pre[place]

                elif self.pre[place] > self.post[place]:
                    self.tests[place] = self.post[place]
                    abs_delta = self.pre[place] - self.post[place]
                    self.inputs[place], self.delta[place] = abs_delta, -abs_delta

                elif self.post[place] > self.pre[place]:
                    self.tests[place] = self.pre[place]
                    abs_delta = self.post[place] - self.pre[place]
                    self.outputs[place], self.delta[place] = abs_delta, abs_delta

                if state_equation:
                    place.input_transitions.add(self)
                    place.output_transitions.add(self)

            elif place in self.pre:
                self.inputs[place] = self.pre[place]
                self.delta[place] = -self.pre[place]

                if state_equation:
                    place.output_transitions.add(self)

            else:
                self.outputs[place] = self.post[place]
                self.delta[place] = self.post[place]

                if state_equation:
                    place.input_transitions.add(self)

            if state_equation and place in self.delta:
                place.delta[self] = self.delta[place]


class Marking:
    """ Marking.

    Attributes
    ----------
    tokens : dict of Place: int
        Number of tokens associated to the places.
    """

    def __init__(self, tokens: Optional[dict[Place, int]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        tokens : dict of Place: int, optional
            Number of tokens associated to the places.
        """
        if tokens is None:
            tokens = {}
        self.tokens: dict[Place, int] = tokens

    def __str__(self) -> str:
        """ Marking to textual format.

        Returns
        -------
        str
            .net format.
        """
        text = ""

        for place, marking in self.tokens.items():
            if marking > 0:
                text += " {}({})".format(str(place.id), marking)

        if text == "":
            text = " empty marking"

        return text

    def smtlib(self, k: int = None) -> str:
        """ Assert the marking.

        Parameters
        ----------
        k : int, optional
            Order.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda pl: "(assert (= {} {}))\n".format(pl.smtlib(k), self.tokens[pl]), self.tokens.keys()))

    def smtlib_trap_initially_marked(self) -> str:
        """ Assert that places in the trap must be initially marked.
            SMT-LIB format
        """
        marked_places = list(
            filter(lambda pl: self.tokens[pl] > 0, self.tokens))

        if not marked_places:
            return "(assert false)\n"

        smt_input = ' '.join(map(lambda pl: pl.id, marked_places))

        if len(marked_places) > 1:
            smt_input = "(or {})".format(smt_input)

        return "(assert {})\n".format(smt_input)

    def smtlib_consider_unmarked_places_for_trap(self) -> str:
        """ Consider unmarked places for trap candidates.

        Returns
        -------
        str
            SMT-LIB format.
        """
        marked_places = list(
            filter(lambda pl: self.tokens[pl] > 0, self.tokens))

        if not marked_places:
            return ""

        return ''.join(map(lambda pl: "(assert (not {}))\n".format(pl.id), marked_places))


class NUPN:
    """ NUPN.

    Attributes
    ----------
    unit_safe : bool
        Unit-safe pragma.
    root : Unit
        Root unit.
    units : dict of str: Unit
        Finite set of units (identified by ids).
    """

    def __init__(self, pnml_filename: str) -> None:
        """ Initializer.

        Parameters
        ----------
        pnml_filename : str
            PNML filename (.pnml format).
        """
        # Unit-safe pragma
        self.unit_safe: bool = False

        # Root
        self.root: Unit = None

        # Unit ids associated to the corresponding unit object
        self.units: dict[str, Unit] = {}

        # Parse toolspecific section
        self.parse_pnml(pnml_filename)

    def __str__(self) -> str:
        """ NUPN to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        # Description
        text = "# NUPN\n"
        text += "# Unit-safe: {}\n".format(self.unit_safe)
        text += "# Root: {}\n".format(self.root.id)

        # Subunits
        text += '\n'.join(map(str, self.units.values()))

        return text

    def smtlib_local_constraints(self) -> str:
        """ Declare units and assert local constraints.
            
        Returns
        -------
        str
            SMT-LIB format.
        """
        return ''.join(map(lambda unit: unit.smtlib(), self.units.values()))

    def smtlib_hierarchy_constraints(self) -> str:
        """ Assert hierarchy constraints.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        paths = self.root.compute_paths()

        for path in paths:
            if len(path) > 1:
                smt_input += "(assert (<= (+ {}) 1))\n".format(
                    ' '.join(map(lambda unit: unit.id, path)))

        return smt_input

    def parse_pnml(self, filename: str) -> None:
        """ Toolspecific section parser.

        Parameters
        ----------
        filename : str
            Petri net filename (.pnml format).
        """
        xmlns = "{http://www.pnml.org/version-2009/grammar/pnml}"
        ET.register_namespace(
            '', "http://www.pnml.org/version-2009/grammar/pnml")

        tree = ET.parse(filename)
        root = tree.getroot()
        # Check if the net is known to be unit-safe
        structure = root.find(xmlns + "net/" + xmlns + "page/" +
                              xmlns + "toolspecific/" + xmlns + "structure")

        # Exit if no NUPN inforation
        if structure is None:
            return

        # Get unit safe pragma
        self.unit_safe = structure.attrib["safe"] == "true"
        if not self.unit_safe:
            return

        # Get root unit
        self.root = self.get_unit(structure.attrib["root"])

        # Get NUPN information
        for unit in structure.findall(xmlns + 'unit'):

            # Get name
            name = unit.attrib["id"]

            # Get places
            pnml_places = unit.find(xmlns + 'places')
            places = {place for place in pnml_places.text.split(
            )} if pnml_places is not None and pnml_places.text else set()

            # Get subunits
            pnml_subunits = unit.find(xmlns + 'subunits')
            subunits = {self.get_unit(subunit) for subunit in pnml_subunits.text.split(
            )} if pnml_subunits is not None and pnml_subunits.text else set()

            # Create new unit
            new_unit = self.get_unit(name)
            new_unit.places = places
            new_unit.subunits = subunits

    def get_unit(self, unit: str) -> Unit:
        """ Return the corresponding unit,
            or create one if does not exist.

        Parameters
        ----------
        unit : str
            Unit id.

        Returns
        -------
        unit
            Corresponding unit (fresh if did not exist)
        """
        if unit in self.units:
            return self.units[unit]

        new_unit = Unit(unit)
        self.units[unit] = new_unit

        return new_unit


class Unit:
    """ NUPN.

    Parameters
    ----------
    id : str
        An identifier.
    places : set of str
        A finite set of local places (identifiers).
    subunits : set of Unit
        A finite set of subunits.
    """

    def __init__(self, id: str) -> None:
        """ Initializer.

        Parameters
        ----------
        id : str
            An identifier.
        """
        # Id
        self.id: str = id

        # Set of places
        self.places: set[str] = set()

        # Set of subunits
        self.subunits: set[Unit] = set()

    def __str__(self) -> str:
        """ Unit to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return "# {}: [{}] - [{}]".format(self.id, ' '.join(self.places), ' '.join(map(lambda subunit: subunit.id, self.subunits)))

    def smtlib(self) -> str:
        """ Declare the unit and assert the local constraint.
            
        Returns
        -------
        str
            SMT-LIB format.
        """
        if not self.places:
            return ""

        # Declaration
        smt_input = "(declare-const {} Int)\n".format(self.id)

        # Unit content
        smt_input_places = ' '.join(self.places)
        if len(self.places) > 1:
            smt_input_places = "(+ {})".format(smt_input_places)
        smt_input += "(assert (= {} {}))\n".format(self.id, smt_input_places)

        # Assert safe unit definition
        smt_input += "(assert (<= {} 1))\n".format(self.id)

        return smt_input

    def compute_paths(self) -> list[list[Unit]]:
        """ Recursively compute hierarchical paths.

        Returns
        -------
        list of list of Unit
            List of paths.
        """
        if not self.subunits:
            if self.places:
                return [[self]]
            else:
                return [[]]

        paths = [
            path for subunit in self.subunits for path in subunit.compute_paths()]

        if self.places:
            for path in paths:
                path.append(self)

        return paths
