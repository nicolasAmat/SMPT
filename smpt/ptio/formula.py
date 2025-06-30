"""
Formula Module

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
__version__ = "5.0"

from abc import ABC, abstractmethod
from collections import Counter, deque
from itertools import product
from operator import eq, ge, gt, le, lt, ne
from os import fsync, remove
from re import search, split
from tempfile import NamedTemporaryFile
from typing import Any, Optional, Sequence
from uuid import uuid4
from xml.etree.ElementTree import Element, parse

from smpt.interfaces.octant import project
from smpt.interfaces.z3 import Z3
from smpt.ptio.ptnet import Marking, PetriNet, Place
from smpt.ptio.verdict import Verdict

TRANSLATION_COMPARISON_OPERATORS = {
    '=': eq,
    '<=': le,
    '>=': ge,
    '<': lt,
    '>': gt,
    'distinct': ne
}

NEGATION_COMPARISON_OPERATORS = {
    '=': 'distinct',
    '<=': '>',
    '>=': '<',
    '<': '>=',
    '>': '<=',
    'distinct': '='
}

COMMUTATION_COMPARISON_OPERATORS = {
    '=': '=',
    '<=': '>=',
    '>=': '<=',
    '<': '>',
    '>': '<',
    'distinct': 'distinct'
}

NEGATION_BOOLEAN_OPERATORS = {
    'and': 'or',
    'or': 'and'
}

BOOLEAN_OPERATORS_TO_MINIZINC_WALK = {
    'not': '-',
    'and': '/\\',
    'or': '\\/'
}

COMPARISON_OPERATORS_TO_WALK = {
    '=': '=',
    '<=': '<=',
    '>=': '>=',
    '<': 'gt',
    '>': 'lt',
    'distinct': '='
}

BOOLEAN_CONSTANTS_TO_WALK = {
    True: 'T',
    False: 'F',
}

XML_TO_COMPARISON_OPERATORS = {
    'integer-le': '<=',
    'integer-ge': '>=',
    'integer-eq': '=',
}

XML_TO_BOOLEAN_OPERATORS = {
    'negation': 'not',
    'conjunction': 'and',
    'disjunction': 'or'
}

LTL_TO_BOOLEAN_OPERATORS = {
    '-': 'not',
    '/\\': 'and',
    '\\/': 'or'
}

XML_TO_BOOLEAN_CONSTANTS = {
    'T': True,
    'F': False
}


class Properties:
    """ Properties.

    Attributes
    ----------
    ptnet : PetriNet
        Associated Petri net.
    ptnet_tfg : PetriNet, optional
        Associated reduced Petri net (TFG).
    ptnet_skeleton : PetriNet, optional
        Skeleton Petri net (if colored).
    formulas : dict of str: Formula
        Set of formulas.
    projected_formulas : dict of str: Formula
        Set of projected formulas.
    invariant : list of Expression
        Formulas found as invariant.
    reachables : list of Expression
        Formulas found as reachable.
    duplicates : dict of str: list of tuple of str, bool
        Duplicate formulas.
    hashes : dict of str: str, optional
        Formula hashes (normal form).
    """

    def __init__(self, ptnet: PetriNet, ptnet_tfg: Optional[PetriNet] = None, ptnet_skeleton: Optional[PetriNet] = None, xml_filename: Optional[str] = None, fireability: bool = False, simplify: bool = False, answered: Optional[set[str]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet : PetriNet
            Associated Petri net.
        ptnet_tfg : PetriNet, optional
            Associated reduced Petri net (TFG).
        ptnet_skeleton : PetriNet, optional
            Skeleton Petri net (if colored).
        xml_filename : str, optional
            Path to formula file (.xml format).
        fireability : bool, optional
            Fireability mode.
        simplify : bool, optional
            Enable simplification formula using z3.
        answered : set of str
            Skip already answered queries (used after running hwalk).
        """
        self.ptnet: PetriNet = ptnet
        self.ptnet_tfg: Optional[PetriNet] = ptnet_tfg
        self.ptnet_skeleton: Optional[PetriNet] = ptnet_skeleton

        self.formulas: dict[str, Formula] = {}
        self.projected_formulas: dict[str, Formula] = {}

        self.invariant: list[Expression] = []
        self.reachable: list[Expression] = []

        self.duplicates: dict[str, list[tuple[str, bool]]] = {}
        self.hashes: Optional[dict[str, str]] = None 

        if xml_filename is not None:
            self.parse_xml(xml_filename, fireability=fireability, simplify=simplify, answered=answered)

    def __str__(self) -> str:
        """ Properties to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        text = ""

        for formula_id, formula in self.formulas.items():
            text += "-> Property {}\n{}\n\n".format(formula_id, formula)

        return text

    def smtlib(self) -> str:
        """ Assert the properties.

        Note
        ----
        Debugging method.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        for formula_id, formula in self.formulas.items():
            smt_input += "; -> Property {}\n{}\n".format(formula_id, formula.smtlib())

        return smt_input

    def minizinc(self) -> str:
        """ Assert the properties.

        Note
        ----
        Debugging method.

        Returns
        -------
        str
            MiniZinc format.
        """
        minizinc_input = ""

        for formula_id, formula in self.formulas.items():
            minizinc_input += "; -> Property {}\n{}\n".format(formula_id, formula.minizinc())

        return minizinc_input

    def parse_xml(self, filename: str, fireability: bool = False, simplify: bool = False, answered: Optional[set[str]]= None) -> None:
        """ Properties parser.

        Parameters
        ----------
        filename : str
            Path to formula file (.xml format).
        fireability : bool, optional
            Fireability mode.
        simplify : bool, optional
            Enable simplification formula using z3.
        answered : set of str
            Skip already answered queries (used after running hwalk).
        """
        tree = parse(filename)
        properties_xml = tree.getroot()

        for property_xml in properties_xml:
            property_id = property_xml[0].text

            if answered is not None and property_id in answered:
                continue

            formula_xml = property_xml[2]
            self.add_formula(Formula(self.ptnet, ptnet_skeleton=self.ptnet_skeleton, formula_xml=formula_xml, fireability=fireability, simplify=simplify), property_id, check_duplicates=simplify)

        # Free hashes
        self.hashes = None

    def add_formula(self, formula: Formula, property_id: Optional[str] = None, check_duplicates: bool = False, projection: bool = False) -> None:
        """ Add a formula.

        Note
        ----
        Generate a random property id if not provided.
    
        Parameters
        ----------
        formula : Formula
            Formula to add.
        property_id : str, optional
            Property id.
        check_duplicates : bool, optional
            Check duplicates.
        projection : bool, optional
            Add projection.
        """
        if property_id is None:
            property_id = str(uuid4())

        formula.identifier = property_id

        if check_duplicates and self.ptnet is not None:

            # Initialize hashes dictionary
            if self.hashes is None:
                self.hashes = {}

            # Compute hash
            nf_hash = formula.P.normal_form_hash()

            # Check if already exists
            if nf_hash in self.hashes:
                # Get equivalent id and if it its negation
                equivalent_id = self.hashes[nf_hash]
                negation = formula.property_def != self.formulas[equivalent_id].property_def
                
                if property_id in self.duplicates:
                    equivalences = [(prev_property_id, prev_negation ^ negation) for (prev_property_id, prev_negation) in self.duplicates[property_id]]
                    equivalences.append((property_id, negation))
                    del self.duplicates[property_id]
                else:
                    equivalences = [(property_id, negation)]

                if equivalent_id in self.duplicates:
                    self.duplicates[equivalent_id] += equivalences
                else:
                    self.duplicates[equivalent_id] = equivalences

                # Delete from formulas
                if property_id in self.formulas:
                    del self.formulas[property_id]
                # Exit (not add to formulas)
                return
            
            else:
                # Add hash
                self.hashes[nf_hash] = property_id

        if not projection:
            self.formulas[property_id] = formula
        else:
            self.projected_formulas[property_id] = formula

    def add_ltl_formula(self, ltl_formulas: str) -> None:
        """ Parse and add reachability formula (.ltl format).

        Parameters
        ----------
        ltl_formulas : str
            Reachability formula (.ltl format)
        """
        property_id = "LTLFormula"
        formula = Formula(self.ptnet, identifier=property_id)
        formula.parse_ltl(ltl_formulas)
        self.add_formula(formula, property_id)

    def add_deadlock_formula(self) -> None:
        """ Add deadlock formula.
        """
        property_id = "ReachabilityDeadlock"
        formula = Formula(self.ptnet, identifier=property_id)
        formula.generate_deadlock()
        self.add_formula(formula, property_id)

    def add_quasi_live_formula(self, quasi_live_transitions: str) -> None:
        """ Add quasi-liveness formula.

        Parameters
        ----------
        quasi_live_transitions : str
            Comma separated list of transition names.
        """
        property_id = "Quasi-liveness-{}".format(quasi_live_transitions)
        transitions = quasi_live_transitions.replace('#', '.').replace('{', '').replace('}', '').split(',')
        formula = Formula(self.ptnet, identifier=property_id)
        formula.generate_quasi_liveness(transitions)
        self.add_formula(formula, property_id)

    def add_reachability_formula(self, reachable_places: str) -> None:
        """ Add reachability formula.

        Parameters
        ----------
        reachable_places : str
            Comma separated list of place names.
        """
        property_id = "Reachability:-{}".format(reachable_places)
        places = reachable_places.replace('#', '.').replace('{', '').replace('}', '').split(',')
        marking = {self.ptnet.places[pl]: 1 for pl in places}
        formula = Formula(self.ptnet, identifier=property_id)
        formula.generate_reachability(marking)
        self.add_formula(formula, property_id)

    def select_queries(self, queries: str) -> None:
        """ Select queries of a given comma-separated list.

        Parameters
        ----------
        queries : str
            List of queries.
        """
        indices = set(map(int, queries.split(',')))
        self.formulas = {property_id: formula for index, (property_id, formula) in enumerate(self.formulas.items()) if index in indices}

    def dnf(self) -> Properties:
        """ Convert all formulas to Disjunctive Normal Form (DNF).

        Returns
        -------
        Properties
            Return self.
        """
        for formula_id in self.formulas:
            self.formulas[formula_id] = self.formulas[formula_id].dnf()

        return self

    def generate_walk_files(self) -> None:
        """ Generated temporary files in Walk format (.ltl).
        """
        for formula in self.formulas.values():
            formula.generate_walk_file()

    def remove_walk_files(self) -> None:
        """ Delete temporary files.
        """
        for formula in self.formulas.values():
            formula.remove_walk_file()
        for formula in self.projected_formulas.values():
            formula.remove_walk_file()

    def generate_parikh_files(self) -> None:
        """ Generated temporary Parikh files.
        """
        for property_id in self.formulas.keys():
            if property_id in self.projected_formulas and self.projected_formulas[property_id].shadow_complete:
                self.projected_formulas[property_id].generate_parikh_file()
            else:
                self.formulas[property_id].generate_parikh_file()

    def remove_parikh_files(self) -> None:
        """ Delete temporary files.
        """
        for formula in self.formulas.values():
            formula.remove_parikh_file()

    def tautologies(self, projection: bool = False) -> list[tuple[str, str]]:
        """ Returns tautologies (or contractions) and remove them.

        Parameters
        ----------
        projection : bool, optional
            Check projected formulas.

        Returns
        -------
        list of tuple of str, str
            Tautologies (identifier, verdict)
        """
        verdicts: list[tuple[str, str]] = []
        to_remove: set[str] = set()

        formulas_to_check = self.projected_formulas if projection else self.formulas
        for property_id, formula in formulas_to_check.items():
            result = formula.R.tautology()
            if result is not None:
                to_remove.add(property_id)
                if result == True:
                    verdicts.append((property_id, self.result(property_id, Verdict.CEX, tautology=True)))
                elif result == False:
                    verdicts.append((property_id, self.result(property_id, Verdict.INV, tautology=True)))
        
        self.formulas = {property_id: formula for property_id, formula in self.formulas.items() if property_id not in to_remove}

        if projection:
            self.formulas_projected = {property_id: formula for property_id, formula in self.projected_formulas.items() if property_id not in to_remove}

        return verdicts

    def project(self, ptnet_tfg: PetriNet, drop_incomplete: bool = False, timeout: int = 3, show_projection: bool = False, save_projection: Optional[str] = None, show_time: bool = False, show_shadow_completeness: bool = False, debug: bool = False) -> None:
        """ Generate projection formulas (.ltl format).

        Parameters
        ----------
        ptnet_tfg : Petri Net
            Petri Net TFG.
        drop_incomplete : bool, optional
            Drop incomplete projections.
        timeout : int, optional
            Projection timeout.
        show_projection : bool, optional
            Show projected formulas.
        save_projection : str, optional
            Save projected formulas.
        show_time : bool, optional
            Show time flag.
        show_shadow_completeness : bool, optional
            Show shadow-completeness flag. 
        debug : bool, optional
            Debugging flag.
        """
        # Run projections
        projections = project(ptnet_tfg.filename, list(self.formulas.values()), timeout=timeout, show_time=show_time, show_shadow_completeness=show_shadow_completeness)

        # Iterate over projections
        for (projection, complete), property_id in zip(projections, list(self.formulas)):

            if projection is None or (drop_incomplete and not complete):
                continue

            # Get original formula
            formula = self.formulas[property_id]

            # Create new formula
            projected_formula = Formula(ptnet_tfg, identifier=property_id)

            # Set shadow-completeness
            projected_formula.shadow_complete = complete

            # Simplification query
            support = {var for var in set(projection.replace('(', ' ').replace(')', ' ').split()) if not var.isnumeric()} - {'and', 'or', 'not', '>=', '<=', '>', '<', '+', '-', '*', 'distinct', 'false', 'true'}
            declaration = ''.join(map(lambda pl: "(declare-const {} Int)\n(assert (>= {} 0))\n".format(pl, pl), support))

            # Parse and add the projected formula
            projected_formula.P = projected_formula.parse_smt(Z3().simplify("{}(assert {})".format(declaration, projection).replace('{', '').replace('}', '')))
            projected_formula.R = StateFormula([projected_formula.P], 'not')
            projected_formula.identifier = formula.identifier
            projected_formula.property_def = formula.property_def

            # Generate walk file
            projected_formula.generate_walk_file()

            # Add formula
            self.add_formula(projected_formula, property_id=property_id, check_duplicates=complete, projection=True)
            
            # Show and save projected formula options
            if show_projection or save_projection:
                output_projection = "<> " + projected_formula.R.walk() if projected_formula.property_def == 'finally' else "[] " + projected_formula.P.walk()
                # Show projected formula if option enabled
                if show_projection:
                    print("# Projection of {}:".format(property_id), output_projection)
                # Save projected formula if option enabled
                if save_projection:
                    with open(save_projection + "/" + property_id + "_projected.ltl", 'w') as fp:
                        fp.write(output_projection)

        # Free hashes
        self.hashes = None
        
    def result(self, property_id: str, verdict: Verdict, tautology: bool = False) -> str:
        """ Return the result (and manage equivalent formulas if there is some).

        Parameters
        ----------
        property_id : str
            Id of the formula.
        verdict : Verdict
            Verdict of the formula.
        tautology : bool, optional
            Is a tautology (do not add to invariant / reachable).

        Returns
        -------
        str
            "TRUE" or "FALSE".
        """
        formula = self.formulas[property_id]
        result = formula.result(verdict)

        if not tautology:
            if result == True:
                if formula.property_def == 'finally':
                    self.reachable.append(formula.R)
                else:
                    self.invariant.append(formula.P)

            elif result == False:
                if formula.property_def == 'finally':
                    self.invariant.append(formula.P)
                else:
                    self.reachable.append(formula.R)

        if property_id in self.duplicates:
            for (equivalent_id, negation) in self.duplicates[property_id]:
                print("\nFORMULA {} {} TECHNIQUES DUPLICATE".format(equivalent_id, str(result ^ negation).upper()))

        return str(result).upper()


class Formula:
    """ Formula.

    Attributes
    ----------
    ptnet : PetriNet
        Associated Petri net.
    ptnet_skeleton : PetriNet, optional
        Skeleton Petri net (if colored).
    identifier : str
        Associated identifier.
    property_def : str
        Property definition ('finally' or 'globally').
    R : Expression, optional
        Feared events.
    P: Expression, optional
        Unfeared events.
    R_skeleton : Expression, optional
        Feared events (on skeleton).
    non_monotonic : bool
        Monotonicity flag.
    walk_filename : str, optional
        Path to .ltl file.
    parikh_filename : str, optional
        Path to an eventual Parikh file.
    show_complete : bool
        Shadow-completeness of the projected formula.
    """

    def __init__(self, ptnet: PetriNet, ptnet_skeleton: Optional[PetriNet] = None, identifier: str = "", formula_xml: Optional[Element] = None, fireability: bool = False, simplify: bool = False) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet : PetriNet
            Associated Petri net.
        ptnet_skeleton : PetriNet, optional
            Skeleton Petri net (if colored).
        identifier : str
            Associated identifier.
        formula_xml : Element, optional
            Formula node (.xml format).
        fireability : bool, optional
            Fireability mode.
        simplify : bool, optional
            Enable simplification formula using z3.

        """
        self.ptnet: PetriNet = ptnet
        self.ptnet_skeleton: Optional[PetriNet] = ptnet_skeleton

        self.identifier: str = identifier
        self.property_def: str = ""

        self.R: Optional[Expression] = None
        self.P: Optional[Expression] = None

        self.R_skeleton: Optional[Expression] = None

        self.non_monotonic: bool = False

        # Temporary files
        self.walk_filename: Optional[str] = None
        self.parikh_filename: Optional[str] = None

        # Misc information
        self.fireability: bool = fireability
        self.shadow_complete: bool = False

        # Parse XML
        if formula_xml is not None:
            _, _, node = formula_xml.tag.rpartition('}')

            if node != 'formula':
                raise ValueError("Invalid formula")

            if simplify:
                simplified_formula = Z3().simplify(self.parse_xml_to_smt(formula_xml[0]))
                f = self.parse_smt(simplified_formula, lets={}, predicates={}) if self.ptnet else None
                f_skeleton = self.parse_smt(simplified_formula, lets={}, predicates={}, skeleton=True) if self.ptnet_skeleton else None
            else:
                f = self.parse_xml(formula_xml[0])
                f_skeleton = self.parse_xml(formula_xml[0], skeleton=True) if self.ptnet_skeleton else None
            
            if self.property_def == 'finally':
                if f:
                    self.R = f
                    self.P = StateFormula([f], 'not')
                self.R_skeleton = f_skeleton
            else:
                if f:
                    self.R = StateFormula([f], 'not')
                    self.P = f
                if f_skeleton:
                    self.R_skeleton = StateFormula([f_skeleton], 'not')

            if self.R:
                self.non_monotonic = not self.R.is_monotonic()

    def parse_xml(self, formula_xml: Element, skeleton: bool = False) -> Optional[Expression]:
        """ Formula parser.

        Parameters
        ----------
        formula_xml : Element
            Formula node (.xml format).
        skeleton : bool, optional
            Parsing skeleton property.

        Returns
        -------
        Expression
            Parsed Element.

        Raises
        ------
        ValueError
            Invalid .xml node.
        """
        _, _, node = formula_xml.tag.rpartition('}')

        if node in ['exists-path', 'all-paths']:
            _, _, child = formula_xml[0].tag.rpartition('}')

            if (node, child) == ('exists-path', 'finally'):
                self.property_def = child

            if (node, child) == ('all-paths', 'globally'):
                self.property_def = child

            return self.parse_xml(formula_xml[0][0], skeleton)

        elif node == 'deadlock':
            return self.generate_deadlock()

        elif node in ['negation', 'conjunction', 'disjunction']:
            return StateFormula([self.parse_xml(operand_xml, skeleton) for operand_xml in formula_xml], node)

        elif node == 'is-fireable':
            clauses: list[Expression] = []
            
            if skeleton:
                # skeleton `.net` input Petri net
                transitions = [self.ptnet.transitions[tr.text] for tr in formula_xml]

            elif self.ptnet.colored:
                # colored `.pnml` input Petri net
                transitions = []
                for colored_transition in formula_xml:
                    transitions += [self.ptnet.transitions[tr] for tr in self.ptnet.colored_transitions_mapping[colored_transition.text]]

            elif self.ptnet.pnml_mapping:
                # `.pnml` input Petri net
                transitions = [self.ptnet.transitions[self.ptnet.pnml_transitions_mapping[tr.text]] for tr in formula_xml]

            else:
                # `.net` input Petri net
                transitions = [self.ptnet.transitions[tr.text.replace('#', '.').replace(',', '.')] for tr in formula_xml]

            for tr in transitions:
                inequalities = []
                for pl, weight in tr.pre.items():
                    inequalities.append(Atom(TokenCount([pl]), IntegerConstant(weight), '>='))

                if not inequalities:
                    clauses.append(BooleanConstant(True))
                elif len(inequalities) == 1:
                    clauses.append(inequalities[0])
                else:
                    clauses.append(StateFormula(inequalities, 'and'))

            if len(clauses) == 1:
                return clauses[0]
            else:
                return StateFormula(clauses, 'or')

        elif node in ['integer-le', 'integer-ge', 'integer-eq']:
            return Atom(self.parse_simple_expression_xml(formula_xml[0], skeleton), self.parse_simple_expression_xml(formula_xml[1], skeleton), XML_TO_COMPARISON_OPERATORS[node])

        else:
            raise ValueError("Invalid .xml node")

    def parse_simple_expression_xml(self, formula_xml: Element, skeleton: bool = False) -> SimpleExpression:
        """ SimpleExpression parser.

        Parameters
        ----------
        formula_xml : Element
            Formula node (.xml format).
        skeleton: bool, optional
            Parsing skeleton property.

        Returns
        -------
        SimpleExpression
            Parsed Element.

        Raises
        ------
        ValueError
            Invalid .xml node.
        """
        _, _, node = formula_xml.tag.rpartition('}')

        if node == 'tokens-count':
            if skeleton:
                # skeleton `.net` input Petri net
                places = [self.ptnet_skeleton.places[place.text] for place in formula_xml]

            elif self.ptnet.colored:
                # colored `.pnml` input Petri net
                places = []
                for colored_place in formula_xml:
                    places += [self.ptnet.places[pl] for pl in self.ptnet.colored_places_mapping[colored_place.text.replace('#', '.')]]

            elif self.ptnet.pnml_mapping:
                # `.pnml` input Petri net
                places = [self.ptnet.places[self.ptnet.pnml_places_mapping[place.text.replace('#', '.')]] for place in formula_xml]

            else:
                # `.net` input Petri net
                places = [self.ptnet.places[place.text.replace('#', '.')] for place in formula_xml]
            return TokenCount(places)

        elif node == 'integer-constant':
            value = int(formula_xml.text)
            return IntegerConstant(value)

        elif node == 'integer-add':
            # Parse addition (e.g., <integer-add><integer-mul>...)
            integer_constant = None
            token_count = None

            for child in formula_xml:
                parsed_child = self.parse_simple_expression_xml(child, skeleton)
                if isinstance(parsed_child, IntegerConstant):
                    if integer_constant is None:
                        integer_constant = parsed_child
                    else:
                        integer_constant.value += parsed_child.value

                elif isinstance(parsed_child, TokenCount):
                    if token_count is None:
                        token_count = parsed_child
                    else:
                        for pl in parsed_child.places:
                            multiplier = parsed_child.multipliers.get(pl, 1)
                            if pl not in token_count.places:
                                token_count.places.append(pl)
                            else:
                                multiplier += token_count.multipliers.get(pl, 1)
                            if multiplier != 1:
                                 token_count.multipliers[pl] = multiplier   
                        token_count.delta += parsed_child.delta

            if token_count is not None and integer_constant is not None:
                token_count.delta += integer_constant.value
                return token_count
            
            return token_count if token_count is not None else integer_constant


        elif node == 'integer-mul':
            # Parse multiplication (e.g., <integer-mul><integer-constant>2</constant><place>X1</place>)
            integer_constant = None
            token_count = None

            for child in formula_xml:
                parsed_child = self.parse_simple_expression_xml(child, skeleton)
                if isinstance(parsed_child, IntegerConstant):
                    if integer_constant is None:
                        integer_constant = parsed_child
                    else:
                        integer_constant.value *= parsed_child.value

                elif isinstance(parsed_child, TokenCount):
                    if token_count is None:
                        token_count = parsed_child
                    else:
                        raise ValueError("Non-linear integer arithmetic")

            if token_count is not None and integer_constant is not None:
                for pl in token_count.places:
                    multiplier = token_count.multipliers.get(pl, 1) * integer_constant.value
                    if multiplier != 1:
                        token_count.multipliers[pl] = multiplier
                return token_count
            else:
                return integer_constant

        else:
            raise ValueError("Invalid .xml node")

    def parse_xml_to_smt(self, formula_xml: Element, support: Optional[set[str]] = None) -> str:
        """ Parse XML formula and return SMT-LIB assertion.

        Parameters
        ----------
        formula_xml : Element
            Formula node (.xml format).
        support : set of str, optional
            Support of the formula.

        Returns
        -------
        str
            SMT-LIB format.
        """
        _, _, node = formula_xml.tag.rpartition('}')

        if node in ['exists-path', 'all-paths']:
            _, _, child = formula_xml[0].tag.rpartition('}')

            if (node, child) == ('exists-path', 'finally'):
                self.property_def = child
                
            if (node, child) == ('all-paths', 'globally'):
                self.property_def = child

            support = set()
            formula = self.parse_xml_to_smt(formula_xml[0][0], support)

            if self.fireability:
                return ''.join(map(lambda var: "(declare-const {} Bool)\n".format(var), support)) + "(assert {})\n".format(formula)
            else: 
                return ''.join(map(lambda var: "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var), support)) + "(assert {})\n".format(formula)

        elif node in ['negation', 'conjunction', 'disjunction']:
            return "({} {})".format(XML_TO_BOOLEAN_OPERATORS[node], ' '.join([self.parse_xml_to_smt(operand_xml, support) for operand_xml in formula_xml]))

        elif node in ['integer-le', 'integer-ge', 'integer-eq']:
            return "({} {} {})".format(XML_TO_COMPARISON_OPERATORS[node], self.parse_xml_to_smt(formula_xml[0], support), self.parse_xml_to_smt(formula_xml[1], support))

        elif node == 'is-fireable':
            for var in formula_xml:
                support.add(var.text)
            return "(or {})".format(' '.join(map(lambda el: el.text, formula_xml))) if len(formula_xml) > 1 else formula_xml[0].text

        elif node == 'tokens-count':
            for var in formula_xml:
                support.add(var.text)
            return "(+ {})".format(' '.join(map(lambda el: el.text, formula_xml))) if len(formula_xml) > 1 else formula_xml[0].text

        elif node == 'integer-constant':
            return formula_xml.text

        else:
            raise ValueError("Invalid .xml node")

    def smt_expand_fireability(self, tr: str, predicates: dict[str, SimpleExpression], skeleton: bool = False) -> SimpleExpression:
        """ Helper for parsing simplified formula (fireability part).

        Parameters
        ----------
        tr : str
            Transition to parse.
        lets : dict of str: SimpleExpression
            Lets associations.
        predicates : dict of str: SimpleExpression
            Memoization of expanded predicates.
        skeleton : bool, optional
            Parsing skeleton property.
        """
        # Check if memoized
        if tr in predicates:
            return predicates[tr]

        clauses: list[Expression] = []

        if skeleton:
            # skeleton `.net` input Petri net
            transitions = [self.ptnet_skeleton.transitions[tr]]

        elif self.ptnet.colored:
            # colored `.pnml` input Petri net
            transitions = [self.ptnet.transitions[tr_blind] for tr_blind in self.ptnet.colored_transitions_mapping[tr]]

        elif self.ptnet.pnml_mapping:
            # `.pnml` input Petri net
            transitions = [self.ptnet.transitions[self.ptnet.pnml_transitions_mapping[tr]]]

        else:
            # `.net` input Petri net
            transitions = [self.ptnet.transitions[tr.replace('#', '.').replace(',', '.')]]

        for transition in transitions:
            inequalities = []
            for pl, weight in transition.pre.items():
                inequality = Atom(TokenCount([pl]), IntegerConstant(weight), '>=')
                inequalities.append(inequality)

            if not inequalities:
                clauses.append(BooleanConstant(True))
            elif len(inequalities) == 1:
                clauses.append(inequalities[0])
            else:
                clauses.append(StateFormula(inequalities, 'and'))

        predicate: SimpleExpression = clauses[0] if len(clauses) == 1 else StateFormula(clauses, 'or')
        
        # Memoize and returns
        if tr not in predicates:
            predicates[tr] = predicate
        return predicate

    def smt_expand_cardinality(self, l: Any, lets: dict[str, SimpleExpression], predicates: dict[str, SimpleExpression], places: Optional[list[Place]] = None, multipliers: Optional[dict[Place, int]] = None, constants: Optional[list[int]] = None, skeleton: bool = False) -> Optional[SimpleExpression]:
            """ Helper for parsing simplified formula (cardinality part).
            """
            if places is None:
                places, multipliers, constants = [], {}, []
                instantiate = True
            else:
                instantiate = False

            if type(l) is not list:
                element = str(l)
                if element in lets:
                    return lets[element]
                elif element.isnumeric():
                    constants.append(int(element))
                else:
                    if skeleton:
                        # skeleton `.net` input Petri net
                        places.append(self.ptnet_skeleton.places[element])

                    elif self.ptnet.colored:
                        # colored `.pnml` input Petri net
                        places += [self.ptnet.places[pl] for pl in self.ptnet.colored_places_mapping[element.replace('#', '.')]]

                    elif self.ptnet.pnml_mapping:
                        # `.pnml` input Petri net
                        places.append(self.ptnet.places[self.ptnet.pnml_places_mapping[element]])

                    else:
                        # `.net` input Petri net
                        places.append(self.ptnet.places[element.replace('#', '.')])

            elif str(l[0]) == '+':
                for expr in l[1:]:
                    self.smt_expand_cardinality(expr, lets, predicates, places=places, multipliers=multipliers, constants=constants, skeleton=skeleton)

            elif str(l[0]) == '*':
                multipliers_place: list[Place] = []
                multipliers_constant: list[int] = []
                for expr in l[1:]:
                    self.smt_expand_cardinality(expr, lets, predicates, places=multipliers_place, multipliers=None, constants=multipliers_constant, skeleton=skeleton)
                coefficient = 1
                for num in multipliers_constant:
                    coefficient *= num
                for place in multipliers_place:
                    multipliers[place] = coefficient

            elif str(l[0]) == '-':
                constants.append(- int(l[1]))
            else:
                raise ValueError

            if instantiate:
                if places:
                    return TokenCount(places, delta=sum(constants), multipliers=multipliers)
                else:
                    return IntegerConstant(sum(constants))
            else:    
                return None

    def parse_smt(self, simplified_formula: Any, lets: dict[str, SimpleExpression] = {}, predicates: dict[str, SimpleExpression] = {}, skeleton: bool = False) -> Optional[Expression]:
        """ Parse simplified formula (SMT-LIB format).

        Parameters
        ----------
        simplified_formula : Any
            Result from sexpdata library.
        lets : dict of str: SimpleExpression, optional
            Lets associations.
        predicates : dict of str: SimpleExpression, optional
            Memoization of expanded predicates.
        skeleton : bool, optional
            Parsing skeleton property.
        """
        # Constant, let reference, boolean, transition predicate 
        if type(simplified_formula) is not list:

            element = str(simplified_formula)

            if element.isnumeric():
                return IntegerConstant(int(element))

            elif element in lets:
                return lets[element]

            elif element in ["true", "false"]:
                return BooleanConstant(element == "true")
            else:
                return self.smt_expand_fireability(element, predicates, skeleton)

        # Nested list case
        if len(simplified_formula) == 1:
            return self.parse_smt(simplified_formula[0], lets, predicates, skeleton)

        operator = str(simplified_formula[0])

        # Goals (entry point)
        if operator == "goals":
            return self.parse_smt(simplified_formula[1], lets, predicates, skeleton)

        # Goal or boolean operator
        elif operator in ["goal", "and", "or", "not"]:

            if operator == "goal":
                to_parse = simplified_formula[1:-4]
                operator = "and"
            else:
                to_parse = simplified_formula[1:]

            operands = []

            for expr in to_parse:
                parsed_expr = self.parse_smt(expr, lets, predicates, skeleton)

                # Boolean simplification
                if isinstance(parsed_expr, BooleanConstant):
                    if operator == 'not':
                        return BooleanConstant(not parsed_expr.value)
                    elif (parsed_expr.value == True and operator == 'and') or (parsed_expr.value == False and operator == 'or'):
                        parsed_expr = None
                    elif (parsed_expr.value == True and operator == 'or'):
                        return BooleanConstant(True)
                    elif (parsed_expr.value == False and operator == 'and'):
                        return BooleanConstant(False)

                if parsed_expr is not None:
                    operands.append(parsed_expr)

            if not operands:
                return BooleanConstant(False) if operator in ["or", "not"] else BooleanConstant(True)

            elif operator != "not" and len(operands) == 1:
                return operands[0]
            
            elif operator == 'not' and isinstance(operands[0], StateFormula) and operands[0].operator == 'not':
                return operands[0].operands[0]

            else:
                return StateFormula(operands, operator)

        # Let declaration
        elif operator == "let":
            for lets_statement in simplified_formula[1]:
                lets[str(lets_statement[0])] = self.parse_smt(lets_statement[1], lets, predicates, skeleton)
            return self.parse_smt(simplified_formula[2:], lets, predicates, skeleton)

        # Comparisons
        elif operator in ["<=", ">=", '<', '>', "=", "distinct"]:
            if (operator == "<=" and str(simplified_formula[1]) == '0') or (operator == ">=" and str(simplified_formula[2]) == '0'):
                return None
            return Atom(self.smt_expand_cardinality(simplified_formula[1], lets=lets, predicates=predicates, skeleton=skeleton), self.smt_expand_cardinality(simplified_formula[2], lets=lets, predicates=predicates, skeleton=skeleton), operator)

        # Arithmetic operation
        elif operator in ["+", "*"]:
            return self.smt_expand_cardinality(simplified_formula, lets=lets, predicates=predicates, skeleton=skeleton)

        else:
            raise ValueError

    def parse_ltl(self, formula: str) -> None:
        """ Properties parser.

        Parameters
        ----------
        formula : str
            Formula (.ltl format).

        Returns
        -------
        Expression
            Parsed formula.
        """
        def _tokenize(s):
            tokens = []
            buffer, last = "", ""
            open_brace = False

            for c in s:
                if c == ' ':
                    continue

                elif (c == '/' and last == '\\') or (c == '\\' and last == '/'):
                    if buffer:
                        tokens.append(buffer)
                    tokens.append(last + c)
                    buffer, last = "", ""

                elif (c == '-' and not open_brace) or c in ['(', ')']:
                    if last:
                        tokens.append(buffer + last)
                    tokens.append(c)
                    buffer, last = "", ""

                elif c == '{':
                    open_brace = True

                elif c == '}':
                    open_brace = False

                else:
                    buffer += last
                    last = c

            if last + buffer:
                tokens.append(buffer + last)

            return tokens

        def _member_constructor(member):
            places, integer_constant, multipliers = [], 0, {}
            for element in member.split('+'):
                if element.isnumeric():
                    integer_constant += int(element)
                else:
                    split_element = element.split('*')
                    place = self.ptnet.places[split_element[-1]]
                    places.append(place)

                    if len(split_element) > 1:
                        multipliers[place] = int(split_element[0])

            if places:
                return TokenCount(places, delta=integer_constant, multipliers=multipliers)
            else:
                return IntegerConstant(integer_constant)

        def _check_negation():
            negate = True
            while negate:
                negate = False
                if stack_operator and stack_operator[-1][0] == 'not' and stack_operator[-1][-1] == open_parenthesis:
                    stack_operands[-1][-1] = StateFormula([stack_operands[-1][-1]], stack_operator.pop()[0])
                    negate = True

        # Number of opened parenthesis (not close)
        open_parenthesis = 0

        # Stacks: operators and operands
        stack_operator: deque[tuple[str, int]] = deque()
        stack_operands: deque[list[Expression]] = deque([[]])

        # Current operator
        current_operator = None

        # Parse atom
        parse_atom = False

        # Read spaces at the beginning
        for index, c in enumerate(formula):
            if c != ' ':
                break

        # Parse potential LTL operator
        witness = False
        if index + 2 <= len(formula):
            if formula[index:index+2] == '[]':
                index = index + 2
            if formula[index:index+2] == '<>':
                index = index + 2
                witness = True
        formula = formula[index:]

        for token in _tokenize(formula):

            if token in ['', ' ']:
                continue

            if token == '-':
                token_operator = LTL_TO_BOOLEAN_OPERATORS[token]
                stack_operator.append((token_operator, open_parenthesis))

            elif token in ['/\\', '\\/']:
                # Get the current operator
                token_operator = LTL_TO_BOOLEAN_OPERATORS[token]

                if current_operator != token_operator:
                    if current_operator:
                        # If the current operator is different from the previous one, construct the previous sub-formula
                        stack_operands[-1] = [StateFormula(stack_operands[-1], stack_operator.pop()[0])]
                    # Add the current operator to the stack
                    stack_operator.append((token_operator, open_parenthesis))
                    current_operator = token_operator

            elif token == '(':
                # Increment the number of parenthesis
                open_parenthesis += 1

                # Add new current operands list
                stack_operands.append([])

                # Reset the last operator
                current_operator = None

            elif token == ')':
                # Fail if no open parenthesis previously
                if not open_parenthesis:
                    raise ValueError("Unbalanced parentheses")

                # Decrease the number of open parenthesis
                open_parenthesis -= 1

                # Add to the previous list
                operands = stack_operands.pop()
                if current_operator:
                    stack_operands[-1].append(StateFormula(operands, stack_operator.pop()[0]))
                else:
                    stack_operands[-1].append(operands[0])

                _check_negation()
                current_operator = stack_operator[-1][0] if stack_operator and stack_operator[-1][-1] == open_parenthesis else None

            elif token in ['T', 'F']:
                # Construct BooleanConstant
                stack_operands[-1].append(BooleanConstant(XML_TO_BOOLEAN_CONSTANTS[token]))

            else:
                # Construct Atom
                if search("(<=|>=|<|>|=)", token):
                    if parse_atom:
                        _, operator, right = split("(<=|>=|<|>|=)", token)
                        stack_operands[-1].append(Atom(stack_operands[-1].pop(), _member_constructor(right), operator))
                        _check_negation()
                        parse_atom = False

                    else:
                        left, operator, right = split("(<=|>=|<|>|=)", token)
                        stack_operands[-1].append(Atom(_member_constructor(left), _member_constructor(right), operator))
                        _check_negation()
                else:
                    stack_operands[-1].append(_member_constructor(token))
                    parse_atom = True

        if open_parenthesis:
            raise ValueError("Unbalances parentheses")

        if stack_operator:
            operands = stack_operands.pop()
            operator = stack_operator.pop()[0]
            self.P = StateFormula(operands, operator)
        else:
            operands, operator = None, None
            self.P = stack_operands.pop()[0]

        if operator == 'not':
            self.R = operands[0]
        else:
            self.R = StateFormula([self.P], 'not')

        self.property_def = 'globally'

        if witness:
            self.P, self.R = self.R, self.P
            self.property_def = 'finally'

    def __str__(self) -> str:
        """ Formula to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return "--> R\n{}\n\n--> P\n{}".format(str(self.R), str(self.P))

    def smtlib(self) -> str:
        """ Assert the Formula.

        Note
        ----
        Debugging method.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "; --> R\n{}\n; --> P\n{}".format(self.R.smtlib(assertion=True), self.P.smtlib(assertion=True))

    def minizinc(self) -> str:
        """ Assert the Formula.

        Note
        ----
        Debugging method.

        Returns
        -------
        str
            MiniZinc format.
        """
        return "; --> R\n{}\n; --> P\n{}".format(self.R.minizinc(assertion=True), self.P.minizinc(assertion=True))

    def walk(self) -> str:
        """ Assert the Formula.

        Note
        ----
        Debugging method.

        Returns
        -------
        str
            .ltl format.
        """
        return "; --> P\n{}\n;".format(self.P.walk())

    def generate_walk_file(self) -> None:
        """ Generate temporary file in .ltl format.
        """
        walk_file = NamedTemporaryFile('w', suffix='.ltl', delete=False)
        self.walk_filename = walk_file.name

        walk_file.write(self.P.walk())
        walk_file.flush()

        fsync(walk_file.fileno())
        walk_file.close()

    def remove_walk_file(self) -> None:
        """ Delete temporary file in .ltl format.
        """
        if self.walk_filename is None:
            return

        try:
            remove(self.walk_filename)
        except OSError:
            pass

    def generate_parikh_file(self) -> None:
        """ Generated temporary Parikh files.
        """
        with NamedTemporaryFile(delete=False) as tmpfile:
            self.parikh_filename = tmpfile.name

    def remove_parikh_file(self) -> None:
        """ Delete temporary file.
        """
        if self.parikh_filename is None:
            return

        try:
            remove(self.parikh_filename)
        except OSError:
            pass

    def generate_deadlock(self) -> Expression:
        """ `deadlock` formula generator.

        Returns
        -------
        Expression
            Formula to reach (R).
        """
        clauses_R: list[Expression] = []

        for tr in self.ptnet.transitions.values():
            inequalities_R = []

            for pl, weight in tr.pre.items():
                inequalities_R.append(Atom(TokenCount([pl]), IntegerConstant(weight), '<'))

            if not inequalities_R:
                clauses_R.append(BooleanConstant(False))
            elif len(inequalities_R) == 1:
                clauses_R.append(inequalities_R[0])
            else:
                clauses_R.append(StateFormula(inequalities_R, 'or'))

        self.R = StateFormula(clauses_R, 'and')
        self.P = StateFormula([self.R], 'not')

        self.property_def = 'finally'
        self.non_monotonic = True

        return self.R

    def generate_quasi_liveness(self, transitions: list[str]) -> None:
        """ `quasi-liveness` formula generator.

        Parameters
        ----------
        transitions : list of str
            Transitions to be enabled (one among them).
        """
        clauses_R: list[Expression] = []

        for tr_id in transitions:
            inequalities_R = []

            for pl, weight in self.ptnet.transitions[tr_id].pre.items():
                inequalities_R.append(Atom(TokenCount([pl]), IntegerConstant(weight), '>='))

            if not inequalities_R:
                clauses_R.append(BooleanConstant(True))
            elif len(inequalities_R) == 1:
                clauses_R.append(inequalities_R[0])
            else:
                clauses_R.append(StateFormula(inequalities_R, 'and'))

        self.R = StateFormula(clauses_R, 'or')
        self.P = StateFormula([self.R], 'not')
        self.property_def = 'finally'

    def generate_reachability(self, marking: dict[Place, int]) -> None:
        """ `reachability` formula generator.

        Parameters
        ----------
        marking : dict of Place: int
            Marking to reach.
        """
        clauses_R = []

        for pl, tokens in marking.items():
            clauses_R.append(Atom(TokenCount([pl]), IntegerConstant(tokens), '>='))

        self.R = StateFormula(clauses_R, 'and')
        self.P = StateFormula([self.R], 'not')
        self.property_def = 'finally'

    def dnf(self) -> Formula:
        """ Convert to Disjunctive Normal Form (DNF).

        Returns
        -------
        Formula
            DNF of the Formula.
        """
        formula = Formula(self.ptnet, identifier=self.identifier)
        formula.non_monotonic, formula.property_def = self.non_monotonic, self.property_def
        formula.P, formula.R = self.P.dnf(), self.R.dnf()
        return formula

    def result(self, verdict: Verdict) -> bool:
        """ Return the result according to the reachability of the feared events R.

        Parameters
        ----------
        verdict : Verdict
            Verdict of the formula.

        Returns
        -------
        bool
            Result.
        """
        if self.property_def == 'finally':
            if verdict == Verdict.CEX:
                return True
            elif verdict == Verdict.INV:
                return False

        if self.property_def == 'globally':
            if verdict == Verdict.CEX:
                return False
            elif verdict == Verdict.INV:
                return True

        return None

class SimpleExpression(ABC):
    """ Simple Expression.

    Note
    ----
    Cannot be evaluated to 'TRUE' or 'FALSE'.
    """

    @abstractmethod
    def __str__(self) -> str:
        """ SimpleExpression to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        pass

    @abstractmethod
    def __eq__(self, other: Any) -> bool:
        """ Compare the SimpleExpression for equality.

        Parameters
        ----------
        other : any
            Other object to compare.
        
        Returns
        -------
        bool
            Equality of the object with other.
        """
        pass

    @abstractmethod
    def __hash__(self) -> int:
        """ Hash the SimpleExpression.

        Returns
        -------
        int
            Hash of the Expression.
        """
        pass

    @abstractmethod
    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Assert the SimpleExpression.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        str
            SMT-LIB format.
        """
        pass

    @abstractmethod
    def minizinc(self) -> str:
        """ Assert the SimpleExpression.

        Returns
        -------
        str
            MiniZinc format.
        """
        pass

    @abstractmethod
    def barvinok(self) -> str:
        """ Assert the SimpleExpression.

        Returns
        -------
        str
            Barvinok format.
        """
        pass

    @abstractmethod
    def walk(self) -> str:
        """ Assert the SimpleExpression.

        Returns
        -------
        str
            .ltl format.
        """
        pass

    @abstractmethod
    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> SimpleExpression:
        """ Generalize the SimpleExpression from a delta vector (or saturated_delta).

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        SimpleExpression
            Generalization of the SimpleExpression.
        """
        pass

    @abstractmethod
    def dnf(self) -> SimpleExpression:
        """ Convert to Disjunctive Normal Form (DNF).

        Returns
        -------
        SimpleExpression
            DNF of the SimpleExpression.
        """
        pass

    @abstractmethod
    def eval(self, m: Marking) -> int:
        """ Evaluate the SimpleExpression with marking m.

        Parameters
        ----------
        m : Marking
            Model for evaluation.

        Returns
        -------
        int
            Evaluation of the SimpleExpression at marking m.
        """
        pass

    def normal_form_hash(self, negation: bool = False) -> str:
        """ Hash the SimpleExpression into a normal form (no negation, places sorted, and only <, <=, = , distinct comparators).

        Parameters
        ----------
        negation : bool, optional
            Propagate negation.

        Returns
        -------
        str
            Hash.
        """
        pass


class Expression(SimpleExpression):
    """ Expression.

    Note
    ----
    Can be evaluated to 'TRUE' or 'FALSE'.
    """

    @abstractmethod
    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None, assertion: bool = False, negation: bool = False) -> str:
        """ Assert the Expression.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.
        assertion : bool
            Assertion flag.
        negation : bool
            Negation flag.

        Returns
        -------
        str
            SMT-LIB format.
        """
        pass

    @abstractmethod
    def minizinc(self, assertion: bool = False) -> str:
        """ Assert the Expression.

        Parameters
        ----------
        assertion : bool
            Assertion flag.


        Returns
        -------
        str
            MiniZinc format.
        """
        pass

    @abstractmethod
    def negation(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        """ Return the negation.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        Expression
            Negation of the Expression.
        """
        pass

    @abstractmethod
    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        """ Generalize the SimpleExpression from a delta vector (or saturated_delta).

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        Expression
            Generalization of the SimpleExpression.
        """
        pass

    @abstractmethod
    def dnf(self, negation_propagation: bool = False) -> Expression:
        """ Convert to Disjunctive Normal Form (DNF).

        Parameters
        ----------
        negation_propagation : bool
            Propagate a negation.

        Returns
        -------
        Expression
            DNF of the Expression.
        """
        pass

    @abstractmethod
    def need_saturation(self, current_delta: dict[Place, int]) -> bool:
        """ Return if the Expression possibly implies a saturation following the delta vector.

        Note
        ----
        Pre-condition: DNF.

        Parameters
        ----------
        current_delta : dict of Place: int
            Current delta vector.

        Returns
        -------
        bool
            Need saturation.
        """
        pass

    def is_monotonic(self, negation : bool = False) -> bool:
        """ Is monotonic.

        Parameters
        ----------
        negation : bool, optional
            Negation flag.
        
        Returns
        -------
        bool
            Is monotonic.
        """
        pass

    def tautology(self) -> Optional[bool]:
        """ Is a tautology or a contradiction.

        Returns
        -------
        bool
            `True` if tautology, `False` if contraction, and `None` otherwise.
        """


class StateFormula(Expression):
    """ StateFormula.

    Attributes
    ----------
    operands : list of Expression
        A list of operands.
    operator : str
        A boolean operator (not, and, or).
    """

    def __init__(self, operands: Sequence[Expression], operator: str) -> None:
        """ Initializer.

        Parameters
        ----------
        operands : Sequence[Expression]
            List of operands.
        operator : str
            Operator (not, and, or).

        Raises
        ------
        ValueError
            Invalid operator for a StateFormula.
        """
        self.operands: Sequence[Expression] = operands

        self.operator: str = ''
        if operator in ['not', 'and', 'or']:
            self.operator = operator
        elif operator in ['negation', 'conjunction', 'disjunction']:
            self.operator = XML_TO_BOOLEAN_OPERATORS[operator]
        else:
            raise ValueError("Invalid operator for a state formula")

    def __str__(self) -> str:
        """ StateFormula to textual format.
            
        Returns
        -------
        str
            Debugging format.
        """
        if self.operator == 'not':
            return "(not {})".format(self.operands[0])

        text = " {} ".format(self.operator).join(map(str, self.operands))

        if len(self.operands) > 1:
            text = "({})".format(text)

        return text

    def __eq__(self, other: Any) -> bool:
        """ Compare the StateFormula for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the StateFormula with other.
        """
        if not isinstance(other, StateFormula):
            return NotImplemented
        else:
            return self.operands == other.operands and self.operator == other.operator

    def __hash__(self) -> int:
        """ Hash the StateFormula.

        Returns
        -------
        int
            Hash of the StateFormula.
        """
        return hash((tuple(self.operands), self.operator))

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None, assertion: bool = False, negation: bool = False) -> str:
        """ Assert StateFormula.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.
        assertion : bool
            Assertion flag.
        negation : bool
            Negation flag.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ' '.join(map(lambda operand: operand.smtlib(
            k, delta=delta, saturated_delta=saturated_delta), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            smt_input = "({} {})".format(self.operator, smt_input)

        if negation:
            smt_input = "(not {})".format(smt_input)

        if assertion:
            smt_input = "(assert {})\n".format(smt_input)

        return smt_input

    def smtlib_unsat_core(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Generate the SMT-LIB output to obtain an unsat core.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ""

        for index, operand in enumerate(self.operands):
            smt_input += "(assert (! {} :named lit@c{}))\n".format(
                operand.smtlib(k, delta=delta, saturated_delta=saturated_delta), index)

        return smt_input

    def learned_clauses_from_unsat_core(self, unsat_core: list[str], delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> list[Expression]:
        """ Return the clauses corresponding to a given unsat core.

        Parameters
        ----------
        unsat_core : list of str
            Unsat core.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        list of Expression
            List of clauses corresponding to the unsat core.
        """
        if unsat_core == ['All']:
            return [operand.negation(delta, saturated_delta) for operand in self.operands]
        else:
            return [self.operands[int(lit.split('@c')[1])].negation(delta, saturated_delta) for lit in unsat_core]

    def minizinc(self, assertion: bool = False) -> str:
        """ Assert the StateFormula.

        Returns
        -------
        str
            MiniZinc format.
        """
        if len(self.operands) > 1:
            operator = BOOLEAN_OPERATORS_TO_MINIZINC_WALK[self.operator]
        else:
            operator = ''

        minizinc_input = ' {} '.format(operator).join(
            map(lambda operand: operand.minizinc(), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            minizinc_input = "({})".format(minizinc_input)

        if self.operator == 'not':
            minizinc_input = "(not {})".format(minizinc_input)

        if assertion:
            minizinc_input = "constraint {};\n".format(minizinc_input)

        return minizinc_input

    def barvinok(self) -> str:
        """ Assert the StateFormula.

        Returns
        -------
        str
            Barvinok format.
        """
        barvinok_input = ' {} '.format(self.operator).join(
            map(lambda operand: operand.barvinok(), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            barvinok_input = "({})".format(barvinok_input)

        if self.operator == 'not':
            barvinok_input = "(not {})".format(barvinok_input)

        return barvinok_input

    def walk(self) -> str:
        """ Assert the StateFormula.

        Returns
        -------
        str
            .ltl format.
        """
        if len(self.operands) > 1:
            operator = BOOLEAN_OPERATORS_TO_MINIZINC_WALK[self.operator]
        else:
            operator = ''

        walk_input = ' {} '.format(operator).join(
            map(lambda operand: operand.walk(), self.operands))

        if len(self.operands) > 1 or self.operator == 'not':
            walk_input = "({})".format(walk_input)

        if self.operator == 'not':
            walk_input = "- {}".format(walk_input)

        return walk_input

    def negation(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> StateFormula:
        """ Return the negation of the StateFormula.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        StateFormula
            Negation of the StateFormula. 
        """
        return StateFormula([operand.negation(delta, saturated_delta) for operand in self.operands], NEGATION_BOOLEAN_OPERATORS[self.operator])

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> StateFormula:
        """ Generalize the StateFormula from a delta vector.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        StateFormula
            Generalization of the StateFormula.
        """
        return StateFormula([operand.generalize(delta, saturated_delta) for operand in self.operands], self.operator)

    def dnf(self, negation_propagation: bool = False) -> Expression:
        """ Convert to Disjunctive Normal Form (DNF).

        Parameters
        ----------
        negation_propagation : bool
            Propagate a negation.

        Returns
        -------
        Expression
            DNF of the StateFormula.
        """
        if self.operator == 'not':
            if negation_propagation:
                # DNF(not (not P)) <-> DNF(P)
                return self.operands[0].dnf()
            else:
                # DNF(not P)
                return self.operands[0].dnf(negation_propagation=True)

        elif self.operator == 'and':
            if negation_propagation:
                # DNF(not (P and Q)) <-> DNF((not P) or (not Q))
                return StateFormula([operand.dnf(negation_propagation) for operand in self.operands], 'or').dnf()
            else:
                # DNF(P and Q) <-> (P1 and Q1) or ... or (Pm and Q1) or ... or (Pm and Qn)
                # with (DNF P) = (P1 or ... or Pm) and (DNF Q) = (Q1 or ... or Qn)
                operands = []
                for operand in self.operands:
                    operand_dnf = operand.dnf()
                    if isinstance(operand_dnf, StateFormula):
                        operands.append(operand_dnf.operands)
                    else:
                        operands.append([operand_dnf])

                clauses = []
                for combination in product(*operands):
                    combination_factorized: list[Expression] = []
                    for cube in combination:
                        if isinstance(cube, StateFormula) and cube.operator == 'and':
                            combination_factorized += cube.operands
                        else:
                            combination_factorized.append(cube)
                    clauses.append(StateFormula(combination_factorized, 'and'))

            return StateFormula(clauses, 'or')

        elif self.operator == 'or':
            if negation_propagation:
                # DNF(not (P or Q)) <-> DNF((not P) and (not Q))
                return StateFormula([operand.dnf(negation_propagation) for operand in self.operands], 'and').dnf()
            else:
                # DNF(P and Q) <-> DNF(P) and DNF(Q)
                operands_dnf: list[Expression] = []

                for operand in self.operands:
                    operand_dnf = operand.dnf()
                    if isinstance(operand_dnf, StateFormula):
                        operands_dnf += operand_dnf.operands
                    else:
                        operands_dnf.append(operand_dnf)
                return StateFormula(operands_dnf, 'or')

        else:
            raise ValueError("Invalid operator for a state formula")

    def eval(self, m: Marking) -> bool:
        """ Evaluate the StateFomula with marking m.

        Parameters
        ----------
        m : Marking
            Model for evaluation.

        Returns
        -------
        bool
            Satisfiability of the StateFormula at marking m.
        """
        if self.operator == 'not':
            return not self.operands[0].eval(m)

        elif self.operator == 'and':
            return all(operand.eval(m) for operand in self.operands)

        elif self.operator == 'or':
            return any(operand.eval(m) for operand in self.operands)

        else:
            return False

    def reached_cube(self, m: Marking) -> Expression:
        """ Return a cube satisfied by marking m.

        Note
        ----
        Pre-conditions: DNF and satisfied by m.

        Parameters
        ----------
        m : Marking

        Returns
        -------
        Expression
            Satisfied cube.

        Raises
        ------
        ValueError
            No satisfiable cube.
        """
        if self.operator == 'or':
            for cube in self.operands:
                if cube.eval(m):
                    return cube

            raise ValueError("No satisfiable cube")

        else:
            return self

    def get_cubes(self) -> Sequence[Expression]:
        """ Return cubes.

        Note
        ----
        Pre-condition: DNF.

        Returns
        -------
        list of Expression
            Cubes.
        """
        return self.operands if self.operator == 'or' else [self]

    def need_saturation(self, current_delta: dict[Place, int]) -> bool:
        """ Return if the formula possibly implies a saturation following the delta vector.
            
        Note
        ----
        Pre-condition: DNF.

        Parameters
        ----------
        current_delta : dict of Place: int
            Current delta vector.

        Returns
        -------
        bool
            Need saturation.
        """
        return all(operand.need_saturation(current_delta) for operand in self.operands)
    
    def is_monotonic(self, negation : bool = False) -> bool:
        """ Is monotonic.

        Parameters
        ----------
        negation : bool, optional
            Negation flag.
        
        Returns
        -------
        bool
            Is monotonic.
        """
        return all(operand.is_monotonic(negation ^ (self.operator == 'not')) for operand in self.operands)
    
    def tautology(self) -> Optional[bool]:
        """ Is a tautology or a contradiction.

        Returns
        -------
        bool
            `True` if tautology, `False` if contraction, and `None` otherwise.
        """
        verdicts = []

        for operand in self.operands:
            verdict = operand.tautology()
            if verdict is None:
                return None
            else:
                verdicts.append(verdict)

        if self.operator == 'not':
            return not verdicts[0]

        elif self.operator == 'and':
            return all(verdicts)

        elif self.operator == 'or':
            return any(verdicts)

        else:
            return None
        
    def normal_form_hash(self, negation: bool = False) -> str:
        """ Hash the StateFormula into a normal form (no negation).

        Parameters
        ----------
        negation : bool, optional
            Propagate negation.

        Returns
        -------
        str
            Hash.
        """
        if self.operator == 'not':
            if negation:
                return self.operands[0].normal_form_hash()
            else:
                return self.operands[0].normal_form_hash(negation=True)
        else:
            if negation:
                return '({})'.format(' {} '.format(NEGATION_BOOLEAN_OPERATORS[self.operator]).join(sorted(map(lambda operand: operand.normal_form_hash(negation=True), self.operands))))
            else:
                return '({})'.format(' {} '.format(self.operator).join(sorted(map(lambda operand: operand.normal_form_hash(), self.operands))))


class Atom(Expression):
    """ Atom.

    Attributes
    ----------
    left_operand : Expression
        Left operand.
    right_operand : Expression
        Right operand.
    operator : str
        Operator (=, <=, >=, <, >, distinct).
    """

    def __init__(self, left_operand: SimpleExpression, right_operand: SimpleExpression, operator: str) -> None:
        """ Initializer.

        Parameters
        ----------
        left_operand : SimpleExpression
            Left operand.
        right_operand : SimpleExpression
            Right operand.
        operator : str
            Operator (=, <=, >=, <, >, distinct).

        Raises
        ------
        ValueError
            Invalid operator for an Atom.
        """
        if operator not in ['=', '<=', '>=', '<', '>', 'distinct']:
            raise ValueError("Invalid operator for an atom")

        self.left_operand: SimpleExpression = left_operand
        self.right_operand: SimpleExpression = right_operand

        self.operator: str = operator

        self.monotonic: bool = False
        self.anti_monotonic: bool = False

    def __str__(self) -> str:
        """ Atom to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return "({} {} {})".format(self.left_operand, self.operator, self.right_operand)

    def __eq__(self, other: Any) -> bool:
        """ Compare the Atom for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the Atom with other.
        """
        if not isinstance(other, Atom):
            return NotImplemented
        else:
            return self.left_operand == other.left_operand and self.right_operand == other.right_operand and self.operator == other.operator

    def __hash__(self) -> int:
        """ Hash the Atom.

        Returns
        -------
        int
            Hash of the Atom.
        """
        return hash((self.left_operand, self.operator, self.right_operand))

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None, assertion: bool = False, negation: bool = False) -> str:
        """ Assert the Atom.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.
        assertion : bool
            Assertion flag.
        negation : bool
            Negation flag.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = "({} {} {})".format(self.operator, self.left_operand.smtlib(
            k, delta=delta, saturated_delta=saturated_delta), self.right_operand.smtlib(k, delta=delta, saturated_delta=saturated_delta))

        if negation:
            smt_input = "(not {})".format(smt_input)

        if assertion:
            smt_input = "(assert {})\n".format(smt_input)

        return smt_input

    def smtlib_unsat_core(self, k: Optional[int] = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Generated the SMT-LIB output to obtain an unsat core.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return "(assert (! {} :named lit@c))\n".format(self.smtlib(k, delta=delta, saturated_delta=saturated_delta))

    def learned_clauses_from_unsat_core(self, unsat_core: list[str], delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> list[Expression]:
        """ Return the clauses corresponding to a given unsat core.

        Parameters
        ----------
        unsat_core : list of str
            Unsat core.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        list of Expression
            List of clauses corresponding to the unsat core.
        """
        return [self.negation(delta, saturated_delta)] if unsat_core else []

    def minizinc(self, assertion: bool = False) -> str:
        """ Assert the Atom.

        Parameters
        ----------
        assertion : bool
            Assertion flag.

        Returns
        -------
        str
            MiniZinc format.
        """
        minizinc_input = "({} {} {})".format(
            self.left_operand.minizinc(), self.operator, self.right_operand.minizinc())

        if assertion:
            minizinc_input = "constraint {};\n".format(minizinc_input)

        return minizinc_input

    def barvinok(self) -> str:
        """ Assert the Atom.

        Parameters
        ----------
        assertion : bool
            Assertion flag.

        Returns
        -------
        str
            Barvinok format.
        """
        return "({} {} {})".format(self.left_operand.barvinok(), self.operator, self.right_operand.barvinok())

    def walk(self) -> str:
        """ Assert the Atom.

        Returns
        -------
        str
            .ltl format.
        """
        def place_id(pl):
            return "{{{}}}".format(pl.id) if '-' in pl.id or '.' in pl.id else pl.id

        def walk_token_count(operand):
            self_literals, opposite_literals = [], []
            
            for pl in operand.places:
                if pl not in operand.multipliers or operand.multipliers[pl] == 1:
                    self_literals.append(place_id(pl))
                elif operand.multipliers[pl] > 0:
                    self_literals.extend([place_id(pl) for _ in range(operand.multipliers[pl])])
                else:
                    opposite_literals.extend([place_id(pl) for _ in range(- operand.multipliers[pl])])

            if operand.delta > 0:
                self_literals.append(str(operand.delta))
            elif operand.delta < 0:
                opposite_literals.append(str(- operand.delta))

            return (self_literals, opposite_literals)

        def walk_integer_constant(operand):
            return ([str(operand.value)], []) if operand.value >= 0 else ([], [str(- operand.value)])

        def addition(l):
            if not l:
                return "0"
            else:
                return "{}".format(' + '.join(l))

        (self_left, opposite_left) = walk_token_count(self.left_operand) if isinstance(self.left_operand, TokenCount) else walk_integer_constant(self.left_operand)
        (self_right, opposite_right) = walk_token_count(self.right_operand) if isinstance(self.right_operand, TokenCount) else walk_integer_constant(self.right_operand)

        left = self_left + opposite_right
        right = self_right + opposite_left

        if self.operator in ['<=', '<']:
            walk_input = "{} {} {}".format(addition(left), COMPARISON_OPERATORS_TO_WALK[self.operator], addition(right))
        elif self.operator in ['>=', '>']:
            op = '<=' if self.operator == '>=' else '<'
            walk_input = "{} {} {}".format(addition(right), op, addition(left))
        elif self.operator == '=':
            l, r = addition(left), addition(right)
            walk_input = "({} <= {}) /\ ({} <= {})".format(l, r, r, l)
        
        if self.operator == 'distinct':
            walk_input = "- {}".format(walk_input)

        return walk_input

    def negation(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        """ Return the negation of the Atom.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        Expression
            Negation of the Atom.
        """
        return Atom(self.left_operand.generalize(delta, saturated_delta), self.right_operand.generalize(delta, saturated_delta), NEGATION_COMPARISON_OPERATORS[self.operator])

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        """ Generalize the Atom from a delta vector (or saturated_delta).

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        Expression
            Generalization of the Atom.
        """
        return Atom(self.left_operand.generalize(delta, saturated_delta), self.right_operand.generalize(delta, saturated_delta), self.operator)

    def dnf(self, negation_propagation: bool = False) -> Expression:
        """ Convert to Disjunctive Normal Form (DNF).

        Parameters
        ----------
        negation_propagation : bool
            Propagate a negation.

        Returns
        -------
        Expression
            DNF of the Atom.
        """
        if negation_propagation:
            # DNF(not (P comp Q)) <-> P (not comp) Q
            return Atom(self.left_operand, self.right_operand, NEGATION_COMPARISON_OPERATORS[self.operator]).dnf()
        else:
            # DNF(P comp Q) <-> P comp Q
            if isinstance(self.left_operand, IntegerConstant) and isinstance(self.right_operand, TokenCount):
                # Normalization: TokenCount at left and IntegerConstant at right
                return Atom(self.right_operand, self.left_operand, COMMUTATION_COMPARISON_OPERATORS[self.operator]).dnf()
            else:
                # Compute the monotonicty and anti-monocity of the atom
                if self.operator in ['<', '<=']:
                    self.anti_monotonic = isinstance(self.left_operand, TokenCount) and isinstance(self.right_operand, IntegerConstant)
                elif self.operator in ['>', '>=']:
                    self.monotonic = isinstance(self.left_operand, TokenCount) and isinstance(self.right_operand, IntegerConstant)

                return self

    def eval(self, m: Marking) -> bool:
        """ Evaluate the Atom with marking m.

        Parameters
        ----------
        m : Marking
            Model for evaluation.

        Returns
        -------
        bool
            Satisfiability of the Atom at marking m.
        """
        return TRANSLATION_COMPARISON_OPERATORS[self.operator](self.left_operand.eval(m), self.right_operand.eval(m))

    def need_saturation(self, current_delta: dict[Place, int]) -> bool:
        """ Return if the Atom possibly implies a saturation following the delta vector.

        Note
        ----
        Pre-condition: DNF.

        Parameters
        ----------
        current_delta : dict of Place: int
            Current delta vector.

        Returns
        -------
        bool
            Need saturation.
        """
        return (not self.monotonic and isinstance(self.left_operand, TokenCount) and all(current_delta[pl] < 0 for pl in self.left_operand.places if pl in current_delta)) or (not self.anti_monotonic and isinstance(self.left_operand, TokenCount) and all(current_delta[pl] > 0 for pl in self.left_operand.places if pl in current_delta)) or (not self.monotonic and not self.anti_monotonic)

    def get_cubes(self) -> Sequence[Expression]:
        """ Return cubes.

        Note
        ----
        Pre-condition: DNF.

        Returns
        -------
        list of Expression
            Cubes.
        """
        return [StateFormula([self], 'and')]

    def reached_cube(self, m: Marking) -> Expression:
        """ Return a cube satisfied by marking m.

        Note
        ----
        Pre-conditions: DNF and satisfied by m.

        Parameters
        ----------
        m : Marking
            Note used.

        Returns
        -------
        Expression
            Self.
        """
        return self
    
    def is_monotonic(self, negation : bool = False) -> bool:
        """ Is monotonic.

        Parameters
        ----------
        negation : bool, optional
            Negation flag.
        
        Returns
        -------
        bool
            Is monotonic.
        """
        if isinstance(self.left_operand, IntegerConstant) and isinstance(self.right_operand, IntegerConstant):
            return True
        elif (not negation and self.operator in [">=", ">"]) or (negation and self.operator in ["<=", "<"]): 
            return isinstance(self.left_operand, TokenCount) and isinstance(self.right_operand, IntegerConstant)
        elif (negation and self.operator in [">=", ">"]) or (not negation and self.operator in ["<=", "<"]):
            return isinstance(self.left_operand, IntegerConstant) and isinstance(self.right_operand, TokenCount)
        else:
            return False
        
    def tautology(self) -> Optional[bool]:
        """ Is a tautology or a contradiction.

        Returns
        -------
        bool
            `True` if tautology, `False` if contraction, and `None` otherwise.
        """
        if isinstance(self.left_operand, IntegerConstant) and isinstance(self.right_operand, IntegerConstant):
            return TRANSLATION_COMPARISON_OPERATORS[self.operator](self.left_operand.value, self.right_operand.value)
        
        elif hash(self.left_operand) == hash(self.right_operand):
            return self.operator in [">=", "<=", "="]
        
        return None

    def normal_form_hash(self, negation: bool = False) -> str:
        """ Hash the Atom into a normal form (only <, <=, = , distinct comparators).

        Parameters
        ----------
        negation : bool, optional
            Propagate negation.

        Returns
        -------
        str
            Hash.
        """
        operator = NEGATION_COMPARISON_OPERATORS[self.operator] if negation else self.operator
        
        if operator in ['>', '>=']:
            return '{} {} {}'.format(self.right_operand.normal_form_hash(), COMMUTATION_COMPARISON_OPERATORS[operator], self.left_operand.normal_form_hash())
        else:
            return '{} {} {}'.format(self.left_operand.normal_form_hash(), operator, self.right_operand.normal_form_hash())


class BooleanConstant(Expression):
    """ Boolean constant.

    Attributes
    ----------
    value : bool
        A boolean constant.
    """

    def __init__(self, value: bool) -> None:
        """ Initializer.

        Parameters
        ----------
        value : bool
            A boolean constant.
        """
        self.value: bool = value

    def __str__(self) -> str:
        """ Boolean constant to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return str(self.value)

    def __eq__(self, other: Any) -> bool:
        """ Compare the BooleanConstant for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the BooleanConstant with other.
        """
        if not isinstance(other, BooleanConstant):
            return NotImplemented
        else:
            return self.value == other.value

    def __hash__(self) -> int:
        """ Hash the BooleanConstant.

        Returns
        -------
        int
            Hash of the BooleanConstant.
        """
        return hash(self.value)

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None, assertion: bool = False, negation: bool = False) -> str:
        """ Assert the BooleanConstant.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.
        assertion : bool
            Assertion flag.
        negation : bool
            Negation flag.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = str(self).lower()

        if negation:
            smt_input = "(not {})".format(smt_input)

        if assertion:
            smt_input = "(assert {})\n".format(smt_input)

        return smt_input

    def minizinc(self, assertion: bool = False) -> str:
        """ Assert the BooleanConstant.

        Parameters
        ----------
        assertion : bool, optional
            Assertion flag.

        Returns
        -------
        str
            MiniZinc format.
        """
        minizinc_input = str(self).lower()

        if assertion:
            minizinc_input = "constraint {};\n".format(minizinc_input)

        return minizinc_input

    def walk(self) -> str:
        """ Assert the BooleanConstant.

        Returns
        -------
        str
            .ltl format.
        """
        return BOOLEAN_CONSTANTS_TO_WALK[self.value]

    def negation(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        """ Return the negation of the BooleanConstant.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        Expression
            Negation of the BooleanConstant.
        """
        return BooleanConstant(not self.value)

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        """ Generalize an BooleanConstant from a delta vector (or saturated_delta).

        Parameters
        ----------
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        Expression
            Generalization of the BooleanConstant.
        """
        return self

    def dnf(self, negation_propagation: bool = False) -> Expression:
        """ Convert to Disjunctive Normal Form (DNF).

        Parameters
        ----------
        negation_propagation : bool, optional
            Propagate a negation.

        Returns
        -------
        Expression
            DNF of the BooleanConstant.
        """
        if negation_propagation:
            return self.negation()
        else:
            return self

    def eval(self, m: Marking) -> bool:
        """ Evaluate the BooleanConstant with marking m.

        Parameters
        ----------
        m : Marking
            Not used.

        Returns
        -------
        bool
            Value of the BooleanConstant.
        """
        return self.value

    def need_saturation(self, current_delta: dict[Place, int]) -> bool:
        """ Return if the BooleanConstant possibly implies a saturation following the delta vector.

        Note
        ----
        Pre-condition: DNF.

        Parameters
        ----------
        current_delta : dict of Place: int
            Not used.

        Returns
        -------
        bool
            Need saturation.
        """
        return self.value

    def barvinok(self) -> str:
        raise NotImplementedError
    
    def is_monotonic(self, negation : bool = False) -> bool:
        """ Is monotonic.

        Parameters
        ----------
        negation : bool, optional
            Negation flag.
        
        Returns
        -------
        bool
            Is monotonic.
        """
        return True
    
    def tautology(self) -> Optional[bool]:
        """ Is a tautology or a contradiction.

        Returns
        -------
        bool
            `True` if tautology, `False` if contraction, and `None` otherwise.
        """
        return self.value
    
    def normal_form_hash(self, negation: bool = False) -> str:
        """ Hash the StateFormula into a normal form (no negation).

        Parameters
        ----------
        negation : bool, optional
            Propagate negation.

        Returns
        -------
        str
            Hash.
        """
        return str(not self.value) if negation else str(self.value)


class UniversalQuantification(Expression):
    """ Universal Quantification.

    Attributes
    ----------
    free_variable : list of FreeVariable
        Universally quantified variables.
    formula : Expression
        Quantifier-free formula.
    """

    def __init__(self, free_variables: list[FreeVariable], formula: Expression) -> None:
        """ Initializer.

        Attributes
        ----------
        free_variable : list of FreeVariable
            Universally quantified variables.
        formula : Expression
            Quantifier-free formula.
        """
        self.free_variables: list[FreeVariable] = free_variables
        self.formula: Expression = formula

    def __str__(self) -> str:
        """ UniversalQuantification to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return "(forall ({}) {})".format(' '.join(map(str, self.free_variables)), self.formula)

    def __eq__(self, other: Any) -> bool:
        """ Compare the UniversalQuantification for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the UniversalQuantification with other.
        """
        if not isinstance(other, UniversalQuantification):
            return NotImplemented
        else:
            return set(self.free_variables) == set(other.free_variables) and self.formula == other.formula

    def __hash__(self) -> int:
        """ Hash UniversalQuantification.

        Returns
        -------
        int
            Hash of the UniversalQuantification.
        """
        return hash((tuple(self.free_variables), self.formula))

    def smtlib(self, k: int = None,  delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None, assertion: bool = False, negation: bool = False) -> str:
        """ Assert the UniversalQuantification.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.
        assertion : bool
            Assertion flag.
        negation : bool
            Negation flag.

        Returns
        -------
        str
            SMT-LIB format. 
        """
        # Declaration of the Quantified Variabbles
        smt_input = ' '.join(
            map(lambda var: "({} Int)".format(var.smtlib(k)), self.free_variables))

        # Add `forall` operator
        smt_input = "(forall ({}) {})".format(
            smt_input, self.formula.smtlib(k, delta, saturated_delta))

        # Optionale negation
        if negation:
            smt_input = "(not {})".format(smt_input)

        # Optional assertion
        if assertion:
            smt_input = "(assert {})".format(smt_input)

        return smt_input

    def minizinc(self, assertion: bool = False) -> str:
        raise NotImplementedError

    def barvinok(self) -> str:
        raise NotImplementedError

    def walk(self) -> str:
        raise NotImplementedError

    def negation(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        raise NotImplementedError

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> Expression:
        raise NotImplementedError

    def dnf(self, negation_propagation: bool = False) -> Expression:
        raise NotImplementedError

    def eval(self, m: Marking) -> bool:
        raise NotImplementedError

    def need_saturation(self, current_delta: dict[Place, int]) -> bool:
        raise NotImplementedError

    def is_monotonic(self, negation : bool = False) -> bool:
        raise NotImplementedError
    
    def tautology(self) -> Optional[bool]:
        raise NotImplementedError
    
    def normal_form_hash(self, negation: bool = False) -> str:
        raise NotImplementedError


class TokenCount(SimpleExpression):
    """ Token count.

    Attributes
    ----------
    places : list of Places
        A list of places to sum.
    delta : int
        An offset to add.
    saturated_delta : list of Expression
        A saturated delta.
    multipliers : dict of Place: int, optional
        Place multipliers (missing if 1).
    """

    def __init__(self, places: list[Place], delta: int = 0, saturated_delta: Optional[list[Expression]] = None, multipliers: Optional[dict[Place, int]] = None):
        """ Initializer.

        Parameters
        ----------
        places : list of Places
            A list of places to sum.
        delta : int, optional
            An offset to add (only for projection).
        saturated_delta : list of Expression, optional
            A saturated delta.
        multipliers : dict of Place: int, optional
            Place multipliers (missing if 1).
        """
        self.places: list[Place] = places

        self.delta: int = delta

        if saturated_delta is None:
            saturated_delta = []
        self.saturated_delta: list[Expression] = saturated_delta

        self.multipliers: dict[Place, int] = {}
        if multipliers is not None:
            self.multipliers = multipliers

    def __str__(self) -> str:
        """ TokenCount to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        text = ' + '.join(map(lambda pl: pl.id if pl not in self.multipliers else "({}.{})".format(
            self.multipliers[pl], pl.id), self.places))

        if self.delta:
            text += " {} {}".format(self.sign(), abs(self.delta))

        if self.saturated_delta:
            text += ' + ' + ' + '.join(map(str, self.saturated_delta))

        if self.delta or self.saturated_delta or len(self.places) > 1:
            text = "({})".format(text)

        return text

    def __eq__(self, other: Any) -> bool:
        """ Compare the TokenCount for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the TokenCount with other.
        """
        if not isinstance(other, TokenCount):
            return NotImplemented
        else:
            return self.places == other.places and self.delta == other.delta

    def __hash__(self) -> int:
        """ Hash the TokenCount.

        Returns
        -------
        int
            Hash of the TokenCount.
        """
        return hash((tuple(self.places), self.delta))

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Assert the TokenCount.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        str
            SMT-LIB format.
        """
        def place_smtlib(pl, k):
            return pl.smtlib(k) if pl not in self.multipliers else "(* {} {})".format(pl.smtlib(k), self.multipliers[pl])

        if delta is not None:
            smt_input = ' '.join(map(lambda pl: "(+ {} {})".format(place_smtlib(
                pl, k), delta[pl]) if delta.get(pl, 0) != 0 else place_smtlib(pl, k), self.places))
        elif saturated_delta is not None:
            smt_input = ' '.join(map(lambda pl: "(+ {} {})".format(place_smtlib(pl, k), ' '.join(map(
                lambda delta: delta.smtlib(k), saturated_delta[pl]))) if pl in saturated_delta else place_smtlib(pl, k), self.places))
        else:
            smt_input = ' '.join(
                map(lambda pl: place_smtlib(pl, k), self.places))

        if len(self.places) > 1:
            smt_input = "(+ {})".format(smt_input)

        if self.delta:
            smt_input = "({} {} {})".format(
                self.sign(), smt_input, abs(self.delta))

        if self.saturated_delta:
            smt_input = "(+ {} {})".format(smt_input,
                                           ' '.join(map(lambda delta: delta.smtlib(k), self.saturated_delta)))

        return smt_input

    def minizinc(self) -> str:
        """ Assert the TokenCount.

        Returns
        -------
        str
            MiniZinc format.
        """
        minizinc_input = ' + '.join(map(lambda pl: pl.id if pl not in self.multipliers else "{} * {}".format(
            pl.id, self.multipliers[pl]), self.places))

        if len(self.places) > 1:
            minizinc_input = "({})".format(minizinc_input)

        if self.delta:
            minizinc_input = "({} {} {})".format(minizinc_input, self.sign(), abs(self.delta))

        return minizinc_input

    def barvinok(self) -> str:
        """ Assert the TokenCount (similar than MinZinc format).

        Returns
        -------
        str
            Barvinok format.
        """
        return self.minizinc()

    def walk(self) -> str:
        """ Assert the TokenCount.

        Returns
        -------
        str
            .ltl format.
        """
        def place_id(pl):
            return "{{{}}}".format(pl.id) if '-' in pl.id or '.' in pl.id else pl.id

        walk_input = ' + '.join(map(lambda pl: place_id(pl) if pl not in self.multipliers else "{}*{}".format(self.multipliers[pl], place_id(pl)), self.places))

        if len(self.places) > 1:
            walk_input = "({})".format(walk_input)

        if self.delta:
            walk_input = "({} + {})".format(walk_input, self.delta)

        return walk_input

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> SimpleExpression:
        """ Generalize the TokenCount from a delta vector (or saturated_delta).

        Parameters
        ----------
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        SimpleExpression
            Generalization of the TokenCount.
        """
        generalized_delta = self.delta + sum([delta.get(pl, 0) for pl in self.places]) if delta is not None else self.delta
        generalized_saturated_delta = self.saturated_delta + sum([saturated_delta.get(pl, []) for pl in self.places], []) if saturated_delta is not None else self.saturated_delta

        return TokenCount(self.places, delta=generalized_delta, saturated_delta=generalized_saturated_delta)

    def dnf(self) -> SimpleExpression:
        """ Convert to Disjunctive Normal Form (DNF).

        Returns
        -------
        SimpleExpression
            DNF of the TokenCount.
        """
        # Normalization: lexicographic order
        self.places = sorted(self.places, key=lambda pl: pl.id)

        # DNF(P1 + ... + Pn) = P1 + ... + Pn
        return self

    def sign(self) -> str:
        """ Return the sign of the offset value.

        Returns
        -------
        str
            The sign of the offset value.
        """
        if self.delta < 0:
            return '-'
        else:
            return '+'

    def eval(self, m: Marking) -> int:
        """ Evaluate the subformula with marking m.

        Parameters
        ----------
        m : Marking
            Model for evaluation.

        Returns
        -------
        int
            Satisfiability of the TokenCount at marking m.
        """
        return sum([m.tokens[pl] if pl not in self.multipliers else self.multipliers[pl] * m.tokens[pl] for pl in self.places]) + self.delta
    
    def normal_form_hash(self, negation: bool = False) -> str:
        """ Hash the TokenCount into a normal form (places sorted).

        Parameters
        ----------
        negation : bool, optional
            Propagate negation.

        Returns
        -------
        str
            Hash.
        """
        nf_hash = ' + '.join(map(lambda place: "{}*{}".format(self.multipliers[place], place.id) if place in self.multipliers else place.id, sorted(self.places, key=lambda pl: pl.id)))
        if self.delta:
            nf_hash += ' {}'.format(self.delta)
        return nf_hash


class IntegerConstant(SimpleExpression):
    """ Integer constant.

    Attributes
    ----------
    value : int
        Constant.
    """

    def __init__(self, value: int) -> None:
        """ Initializer.

        Parameters
        ----------
        value : int
            Constant.
        """
        self.value = value

    def __str__(self) -> str:
        """ Integer constant to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return str(self.value)

    def __eq__(self, other) -> bool:
        """ Compare the IntegerConstant for equality.

        Returns
        -------
        bool
            Equality of the IntegerConstant with other.
        """
        if not isinstance(other, IntegerConstant):
            return NotImplemented
        else:
            return self.value == other.value

    def __hash__(self) -> int:
        """ Hash the IntegerConstant.

        Returns
        -------
        int
            Hash of the IntegerConstant.
        """
        return hash(self.value)

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Assert the IntegerConstant.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return str(self)

    def minizinc(self) -> str:
        """ Assert the IntegerConstant.

        Returns
        -------
        str
            MiniZinc format.
        """
        return str(self)

    def barvinok(self) -> str:
        """ Assert the IntegerConstant.

        Returns
        -------
        str
            Barvinok format.
        """
        return str(self)

    def walk(self) -> str:
        """ Assert the IntegerConstant.

        Returns
        -------
        str
            .ltl format.
        """
        return str(self.value)

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> SimpleExpression:
        """ Generalize the IntegerConstant from a delta vector (or saturated_delta).

        Parameters
        ----------
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        SimpleExpression
            Generalization of the IntegerConstant.
        """
        return self

    def dnf(self) -> SimpleExpression:
        """ Convert to Disjunctive Normal Form (DNF).

        Returns
        -------
        SimpleExpression
            DNF of the IntegerConstant.
        """
        # DNF(k) = k
        return self

    def eval(self, m: Marking) -> int:
        """ Evaluate the IntegerConstant with marking m.

        Parameters
        ----------
        m : Marking
            Not used.

        Returns
        -------
        int
            Evaluation of the IntegerConstant at marking m.
        """
        return self.value
    
    def normal_form_hash(self, negation: bool = False) -> str:
        """ Hash the IntegerConstant into a normal form.

        Parameters
        ----------
        negation : bool, optional
            Propagate negation.

        Returns
        -------
        str
            Hash.
        """
        return str(self.value)


class ArithmeticOperation(SimpleExpression):
    """ Arithmetic Operation.

    Attributes
    ----------
    operands : list of 
        A list of operands.
    operator : str
        An operator ('+', '*').
    """

    def __init__(self, operands: list[SimpleExpression], operator: str) -> None:
        """ Initializer.

        Parameters
        ----------
        operands : list of 
            A list of operands.
        operator : str
            An operator (+, *).

        Raises
        ------
        ValueError
            Invalid operator for an ArithmeticOperation.
        """
        if operator not in ['+', '*']:
            raise ValueError("Invalid operator for an arithmetic operation")

        self.operands: list[SimpleExpression] = operands
        self.operator: str = operator

    def __str__(self) -> str:
        """ ArithmeticOperation to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return "(" + " {} ".format(self.operator).join(map(str, self.operands)) + ")"

    def __eq__(self, other: Any) -> bool:
        """ Compare the ArithmeticOperation for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the ArithmeticOperation with other.
        """
        if not isinstance(other, ArithmeticOperation):
            return NotImplemented
        else:
            return self.operator == other.operator and Counter(self.operands) == Counter(other.operands)

    def __hash__(self) -> int:
        """ Hash the ArithmeticOperation.

        Returns
        -------
        int
            Hash of the ArithmeticOperation.
        """
        return hash((tuple(self.operands), self.operator))

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Assert the ArithmeticOperation.

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Replace p by p + delta.
        saturated_delta : dict of Place: list of Expression, optional
            Replace p by p + saturated_delta.

        Returns
        -------
        str
            SMT-LIB format.
        """
        smt_input = ' '.join(map(lambda operand: operand.smtlib(
            k, delta=delta, saturated_delta=saturated_delta), self.operands))

        return "({} {})".format(self.operator, smt_input)

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> SimpleExpression:
        """ Generalize the ArithmeticOperation from a delta vector.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        SimpleExpression
            Generalization of the ArithmeticOperation.
        """
        return self

    def eval(self, m: Marking) -> int:
        if self.operator == '+':
            return sum(op.eval(m) for op in self.operands)
        elif self.operator == '*':
            result = 1
            for op in self.operands:
                result *= op.eval(m)
            return result
        else:
            raise ValueError(f"Unsupported operator '{self.operator}' in ArithmeticOperation.eval")

    def minizinc(self) -> str:
        raise NotImplementedError

    def barvinok(self) -> str:
        raise NotImplementedError

    def walk(self) -> str:
        raise NotImplementedError

    def dnf(self) -> SimpleExpression:
        raise NotImplementedError
    
    def normal_form_hash(self, negation: bool = False) -> str:
        raise NotImplementedError


class FreeVariable(SimpleExpression):
    """ Free Variable.

    Note
    ----
    Extension for the Saturated Transition-Based Generalization used in PDR.

    Attributes
    ----------
    id : str
        An identifier.
    index : int
        Number of the FreeVariable.
    """

    def __init__(self, id: str, index: int) -> None:
        """ Initializer.
        """
        self.id: str = id
        self.index: int = index

    def __str__(self) -> str:
        """ FreeVariable to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        return "k{}".format(self.index)

    def __eq__(self, other: Any) -> bool:
        """ Compare the FreeVariable for equality.

        Parameters
        ----------
        other : any
            Other object to compare.

        Returns
        -------
        bool
            Equality of the FreeVariable with other.
        """
        if not isinstance(other, FreeVariable):
            return NotImplemented
        else:
            return self.id == other.id

    def __hash__(self) -> int:
        """ Hash the FreeVariable.

        Returns
        -------
        int
            Hash of the FreeVariable.
        """
        return hash(self.id)

    def smtlib(self, k: int = None, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> str:
        """ Assert the FreeVariable. 

        Parameters
        ----------
        k : int, optional
            Order.
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        str
            SMT-LIB format.
        """
        return self.id if k is None else "{}@{}".format(self.id, k)

    def smtlib_declare(self, k: Optional[int] = None) -> str:
        """ Declare the FreeVariable.

        Returns
        -------
        str
            SMT-LIB format.
        """
        if k is None:
            return "(declare-const {} Int)\n(assert (>= {} 0))\n".format(self.id, self.id)
        else:
            return "(declare-const {}@{} Int)\n(assert (>= {}@{} 0))\n".format(self.id, k, self.id, k)

    def generalize(self, delta: Optional[dict[Place, int]] = None, saturated_delta: Optional[dict[Place, list[Expression]]] = None) -> SimpleExpression:
        """ Generalize the FreeVariable from a delta vector.

        Parameters
        ----------
        delta : dict of Place: int, optional
            Not used.
        saturated_delta : dict of Place: list of Expression, optional
            Not used.

        Returns
        -------
        SimpleExpression
            Generalization of the FreeVariable.
        """
        return self

    def minizinc(self) -> str:
        raise NotImplementedError

    def barvinok(self) -> str:
        raise NotImplementedError

    def walk(self) -> str:
        raise NotImplementedError

    def dnf(self) -> SimpleExpression:
        raise NotImplementedError

    def eval(self, m: Marking) -> int:
        raise NotImplementedError

    def normal_form_hash(self, negation: bool = False) -> str:
        raise NotImplementedError
