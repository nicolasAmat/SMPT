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
__version__ = "4.0.0"

from abc import ABC, abstractmethod
from collections import Counter, deque
from itertools import product
from operator import eq, ge, gt, le, lt, ne
from os import fsync, remove
from re import search, split, sub
from tempfile import NamedTemporaryFile
from typing import Any, Optional, Sequence
from uuid import uuid4
from xml.etree.ElementTree import Element, parse

from smpt.interfaces.tipx import Tipx
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
    formulas : dict of str: Formula
        Set of formulas.
    projected_formulas : dict of str: Formula
        Set of projected formulas.
    """

    def __init__(self, ptnet: PetriNet, ptnet_tfg: Optional[PetriNet] = None, xml_filename: Optional[str] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet : PetriNet
            Associated Petri net.
        ptnet_tfg : PetriNet, optional
            Associated reduced Petri net (TFG).
        xml_filename : str, optional
            Path to formula file (.xml format).
        """
        self.ptnet: PetriNet = ptnet
        self.ptnet_tfg: PetriNet = ptnet_tfg

        self.formulas: dict[str, Formula] = {}
        self.projected_formulas: dict[str, Formula] = {}

        if xml_filename is not None:
            self.parse_xml(xml_filename)

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
            smt_input += "; -> Property {}\n{}\n".format(
                formula_id, formula.smtlib())

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
            minizinc_input += "; -> Property {}\n{}\n".format(
                formula_id, formula.minizinc())

        return minizinc_input

    def parse_xml(self, filename: str) -> None:
        """ Properties parser.

        Parameters
        ----------
        str
            Path to formula file (.xml format).
        """
        tree = parse(filename)
        properties_xml = tree.getroot()

        for property_xml in properties_xml:
            property_id = property_xml[0].text
            formula_xml = property_xml[2]

            self.add_formula(
                Formula(self.ptnet, formula_xml=formula_xml), property_id)

    def add_formula(self, formula: Formula, property_id: Optional[str] = None) -> None:
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
        """
        if property_id is None:
            property_id = str(uuid4())

        formula.identifier = property_id
        self.formulas[property_id] = formula

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
        transitions = quasi_live_transitions.replace(
            '#', '.').replace('{', '').replace('}', '').split(',')
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
        places = reachable_places.replace('#', '.').replace(
            '{', '').replace('}', '').split(',')
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
        self.formulas = {property_id: formula for index, (property_id, formula) in enumerate(
            self.formulas.items()) if index in indices}

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

    def remove_parikh_files(self) -> None:
        """ Delete temporary files.
        """
        for formula in self.formulas.values():
            formula.remove_parikh_file()

    def project(self, ptnet_tfg: PetriNet, drop_incomplete: bool = False, show_projection: bool = False, save_projection: Optional[str] = None, show_time: bool = False, show_shadow_completeness: bool = False, debug: bool = False) -> None:
        """ Generate projection formulas (.ltl format).

        Parameters
        ----------
        ptnet_tfg : Petri Net
            Petri Net TFG.
        drop_incomplete : bool, optional
            Drop incomplete projections.
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
        # Create TiPX instance
        tipx = Tipx(ptnet_tfg.filename, debug=debug)

        # Run projections
        projections = tipx.project(list(self.formulas.values(
        )), show_time=show_time, show_shadow_completeness=show_shadow_completeness)

        # Iterate over projections
        for (projection, complete), (property_id, formula) in zip(projections, self.formulas.items()):

            if projection is None or (drop_incomplete and not complete):
                continue

            # Create new formula
            projected_formula = Formula(ptnet_tfg, property_id)

            # Set shadow-completeness
            projected_formula.shadow_complete = complete

            # Write the projected formula into a temporary file
            fp_projected_formula = NamedTemporaryFile(
                'w', suffix='.ltl', delete=False)
            projected_formula.walk_filename = fp_projected_formula.name
            fp_projected_formula.write(projection)
            fp_projected_formula.flush()
            fsync(fp_projected_formula.fileno())
            fp_projected_formula.close()

            # Parse and add the projected formula
            projected_formula.parse_ltl(projection)
            projected_formula.identifier = formula.identifier
            projected_formula.property_def = formula.property_def
            self.projected_formulas[property_id] = projected_formula

            if show_projection or save_projection:
                output_projection = "<> " + projected_formula.R.walk() if projected_formula.property_def == 'finally' else "[] " + \
                    projected_formula.P.walk()
                # Show projected formula if option enabled
                if show_projection:
                    print("# Projection of {}:".format(
                        property_id), output_projection)
                # Save projected formula if option enabled
                if save_projection:
                    with open(save_projection + "/" + property_id + ".ltl", 'w') as fp:
                        fp.write(output_projection)


class Formula:
    """ Formula.

    Attributes
    ----------
    ptnet : PetriNet
        Associated Petri net.
    identifier : str
        Associated identifier.
    R : Expression, optional
        Feared events.
    P: Expression, optional
        Unfeared events.
    property_def : str
        Property definition (exists-paths finally, all-paths globally).
    non_monotonic : bool
        Monotonicity flag.
    walk_filename : str, optional
        Path to .ltl file.
    parikh_filename : str, optional
        Path to an eventual Parikh file.
    show_complete : bool
        Shadow-completeness of the projected formula.
    """

    def __init__(self, ptnet: PetriNet, identifier: str = "", formula_xml: Optional[Element] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet : PetriNet
            Associated Petri net.
        identifier : str
            Associated identifier.
        formula_xml : Element, optional
            Formula node (.xml format).
        """
        self.ptnet: PetriNet = ptnet

        self.identifier: str = identifier

        self.R: Optional[Expression] = None
        self.P: Optional[Expression] = None

        self.property_def: str = ""
        self.non_monotonic: bool = False

        self.walk_filename: Optional[str] = None

        # Parikh temporary file management
        self.parikh_filename: Optional[str] = None
        if ptnet.parikh:
            with NamedTemporaryFile(delete=False) as tmpfile:
                self.parikh_filename = tmpfile.name

        self.shadow_complete: bool = False

        if formula_xml is not None:
            _, _, node = formula_xml.tag.rpartition('}')

            if node != 'formula':
                raise ValueError("Invalid formula")

            self.parse_xml(formula_xml[0])

    def parse_xml(self, formula_xml: Element, negation: bool = False) -> Optional[Expression]:
        """ Formula parser.

        Parameters
        ----------
        formula_xml : Element
            Formula node (.xml format).
        negation : bool
            Negation flag.

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
                self.R = self.parse_xml(formula_xml[0][0])
                self.P = StateFormula([self.R], 'not')

            if (node, child) == ('all-paths', 'globally'):
                self.property_def = child
                self.P = self.parse_xml(formula_xml[0][0])
                self.R = StateFormula([self.P], 'not')

            return None

        elif node == 'deadlock':
            return self.generate_deadlock()

        elif node in ['negation', 'conjunction', 'disjunction']:
            negation ^= node == 'negation'
            operands = [self.parse_xml(operand_xml, negation=negation)
                        for operand_xml in formula_xml]
            return StateFormula(operands, node)

        elif node == 'is-fireable':
            clauses: list[Expression] = []

            if self.ptnet.colored:
                # colored `.pnml` input Petri net
                transitions = []
                for colored_transition in formula_xml:
                    transitions += [self.ptnet.transitions[tr]
                                    for tr in self.ptnet.colored_transitions_mapping[colored_transition.text]]

            elif self.ptnet.skeleton:
                # skeleton `.net` input Petri net
                transitions = [self.ptnet.transitions[sub("[^0-9a-zA-Z]", "_", tr.text)] for tr in formula_xml]

            elif self.ptnet.pnml_mapping:
                # `.pnml` input Petri net
                transitions = [
                    self.ptnet.transitions[self.ptnet.pnml_transitions_mapping[tr.text]] for tr in formula_xml]

            else:
                # `.net` input Petri net
                transitions = [self.ptnet.transitions[tr.text.replace(
                    '#', '.').replace(',', '.')] for tr in formula_xml]

            for tr in transitions:
                inequalities = []
                for pl, weight in tr.pre.items():
                    if weight > 0:
                        inequality = Atom(TokenCount(
                            [pl]), IntegerConstant(weight), '>=')
                        if (self.property_def == 'finally' and negation) or (self.property_def == 'globally' and not negation):
                            self.non_monotonic = True
                    else:
                        inequality = Atom(TokenCount(
                            [pl]), IntegerConstant(-weight), '<')
                        if (self.property_def == 'finally' and not negation) or (self.property_def == 'globally' and negation):
                            self.non_monotonic = True
                    inequalities.append(inequality)

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
            left_operand = self.parse_simple_expression_xml(formula_xml[0])
            right_operand = self.parse_simple_expression_xml(formula_xml[1])

            finally_monotonic = self.property_def == 'finally' \
                and ((not negation and isinstance(left_operand, IntegerConstant) and isinstance(right_operand, TokenCount))
                     or (negation and isinstance(left_operand, TokenCount) and isinstance(right_operand, IntegerConstant)))
            globally_monotonic = self.property_def == 'globally' \
                and ((negation and isinstance(left_operand, IntegerConstant) and isinstance(right_operand, TokenCount))
                     or (not negation and isinstance(left_operand, TokenCount) and isinstance(right_operand, IntegerConstant)))

            if not (finally_monotonic or globally_monotonic):
                self.non_monotonic = True

            return Atom(left_operand, right_operand, XML_TO_COMPARISON_OPERATORS[node])

        else:
            raise ValueError("Invalid .xml node")

    def parse_simple_expression_xml(self, formula_xml: Element) -> SimpleExpression:
        """ SimpleExpression parser.

        Parameters
        ----------
        formula_xml : Element
            Formula node (.xml format).
        negation : bool
            Negation flag.

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
            if self.ptnet.colored:
                # colored `.pnml` input Petri net
                places = []
                for colored_place in formula_xml:
                    places += [self.ptnet.places[pl]
                               for pl in self.ptnet.colored_places_mapping[colored_place.text.replace('#', '.')]]

            elif self.ptnet.skeleton:
                # skeleton `.net` input Petri net
                places = [self.ptnet.places[sub("[^0-9a-zA-Z]", "_", place.text)] for place in formula_xml]

            elif self.ptnet.pnml_mapping:
                # `.pnml` input Petri net
                places = [self.ptnet.places[self.ptnet.pnml_places_mapping[place.text.replace(
                    '#', '.')]] for place in formula_xml]

            else:
                # `.net` input Petri net
                places = [self.ptnet.places[place.text.replace(
                    '#', '.')] for place in formula_xml]
            return TokenCount(places)

        elif node == 'integer-constant':
            value = int(formula_xml.text)
            return IntegerConstant(value)

        else:
            raise ValueError("Invalid .xml node")

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

            if token in ['-', '/\\', '\\/']:
                # Get the current operator
                token_operator = LTL_TO_BOOLEAN_OPERATORS[token]

                if current_operator:
                    # If the current operator is different from the previous one, construct the previous sub-formula
                    if current_operator != token_operator:
                        stack_operands[-1] = [StateFormula(
                            stack_operands[-1], stack_operator.pop()[0])]
                else:
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
                    stack_operands[-1].append(StateFormula(operands,
                                              stack_operator.pop()[0]))
                else:
                    stack_operands[-1].append(operands[0])

                current_operator = stack_operator[-1][0] if stack_operator and stack_operator[-1][-1] == open_parenthesis else None

            elif token in ['T', 'F']:
                # Construct BooleanConstant
                stack_operands[-1].append(BooleanConstant(
                    XML_TO_BOOLEAN_CONSTANTS[token]))

            else:
                # Construct Atom
                if search("(<=|>=|<|>|=)", token):
                    if parse_atom:
                        _, operator, right = split("(<=|>=|<|>|=)", token)
                        stack_operands[-1].append(
                            Atom(stack_operands[-1].pop(), _member_constructor(right), operator))
                        parse_atom = False

                    else:
                        left, operator, right = split(
                            "(<=|>=|<|>|=)", token)
                        stack_operands[-1].append(Atom(_member_constructor(
                            left), _member_constructor(right), operator))
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
                if weight > 0:
                    ineq_R = Atom(TokenCount([pl]),
                                  IntegerConstant(weight), '<')
                else:
                    ineq_R = Atom(TokenCount([pl]),
                                  IntegerConstant(-weight), '>=')
                inequalities_R.append(ineq_R)

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
                if weight > 0:
                    ineq_R = Atom(TokenCount([pl]),
                                  IntegerConstant(weight), '>=')
                else:
                    ineq_R = Atom(TokenCount([pl]),
                                  IntegerConstant(-weight), '<')
                    self.non_monotonic = True
                inequalities_R.append(ineq_R)

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
            clauses_R.append(
                Atom(TokenCount([pl]), IntegerConstant(tokens), '>='))

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
        formula = Formula(self.ptnet, self.identifier)
        formula.non_monotonic, formula.property_def = self.non_monotonic, self.property_def
        formula.P, formula.R = self.P.dnf(), self.R.dnf()
        return formula

    def result(self, verdict: Verdict) -> str:
        """ Return the result according to the reachability of the feared events R.

        Parameters
        ----------
        verdict : Verdict
            Verdict of the formula.

        Returns
        -------
        str
            "TRUE" or "FALSE".
        """
        if self.property_def == 'finally':
            if verdict == Verdict.CEX:
                return "TRUE"
            elif verdict == Verdict.INV:
                return "FALSE"

        if self.property_def == 'globally':
            if verdict == Verdict.CEX:
                return "FALSE"
            elif verdict == Verdict.INV:
                return "TRUE"

        return ""


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
        walk_input = "({} {} {})".format(self.left_operand.walk(
        ), COMPARISON_OPERATORS_TO_WALK[self.operator], self.right_operand.walk())

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
                    self.anti_monotonic = isinstance(self.left_operand, TokenCount) and isinstance(
                        self.right_operand, IntegerConstant)
                elif self.operator in ['>', '>=']:
                    self.monotonic = isinstance(self.left_operand, TokenCount) and isinstance(
                        self.right_operand, IntegerConstant)

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

        self.multipliers: dict[Place, int] = multipliers

    def __str__(self) -> str:
        """ TokenCount to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        text = ' + '.join(map(lambda pl: pl.id if self.multipliers is None or pl not in self.multipliers else "({}.{})".format(
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
            return pl.smtlib(k) if self.multipliers is None or pl not in self.multipliers else "(* {} {})".format(pl.smtlib(k), self.multipliers[pl])

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
        minizinc_input = ' + '.join(map(lambda pl: pl.id if self.multipliers is None or pl not in self.multipliers else "{} * {}".format(
            pl.id, self.multipliers[pl]), self.places))

        if len(self.places) > 1:
            minizinc_input = "({})".format(minizinc_input)

        if self.delta:
            minizinc_input = "({} {} {})".format(
                minizinc_input, self.sign(), self.delta)

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

        smt_input = ' + '.join(map(lambda pl: place_id(pl) if self.multipliers is None or pl not in self.multipliers else "{}*{}".format(
            self.multipliers[pl], place_id(pl)), self.places))

        if len(self.places) > 1:
            smt_input = "({})".format(smt_input)

        if self.delta:
            smt_input = "({} {} {})".format(smt_input, self.sign(), self.delta)

        return smt_input

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
        generalized_delta = self.delta + \
            sum([delta.get(pl, 0) for pl in self.places]
                ) if delta is not None else self.delta
        generalized_saturated_delta = self.saturated_delta + sum([saturated_delta.get(
            pl, []) for pl in self.places], []) if saturated_delta is not None else self.saturated_delta

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
        return sum([m.tokens[pl] if self.multipliers is None or pl not in self.multipliers else self.multipliers[pl] * m.tokens[pl] for pl in self.places]) + self.delta


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
        return str(self)

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
