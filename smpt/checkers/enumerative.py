"""
Enumerative Markings Method

Input file format: .aut
Documentation: http://projects.laas.fr/tina//manuals/formats.html

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

from logging import info
from multiprocessing import Queue
from re import split
from sys import exit
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.z3 import Z3
from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import Marking, PetriNet
from smpt.ptio.system import System
from smpt.ptio.verdict import Verdict


class Enumerative(AbstractChecker):
    """ Enumerative markings method.

    Attributes
    ----------
    ptnet : PetriNet
        Initial Petri net.
    ptnet_reduced : PetriNet, optional
        Reduced Petri net.
    system : System, optional
        System of reduction equations.
    formula : Formula
        Reachability formula.
    markings : list of dict of str, int
        Reachable markings.
    solver : Z3
        SMT solver (Z3).
    """

    def __init__(self, path_markings: str, ptnet: PetriNet, formula: Formula, ptnet_reduced: Optional[PetriNet] = None, system: Optional[System] = None, debug: bool = False, solver_pids: Optional[Queue[int]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        path_markings : str
            Path to the list of markings (.aut format).
        ptnet : PetriNet
            Initial Petri net.
        formula : Formula
            Reachability formula.
        ptnet_reduced : PetriNet, optional
            Reduced Petri net.
        system : System, optional
            System of reduction equations.
        debug : bool, optional
            Debugging flag.
        solver_pids : Queue of int, optional
            Queue to share the current PID.
        """
        # Initial Petri net
        self.ptnet: PetriNet = ptnet

        # Reduced Petri net
        self.ptnet_reduced: Optional[PetriNet] = ptnet_reduced

        # System of linear equations
        self.system: Optional[System] = system

        # Formula to study
        self.formula: Formula = formula

        # Reachable markings
        self.markings: list[dict[str, int]] = []
        self.parse_markings(path_markings)

        # SMT solver
        self.debug = debug
        self.solver_pids = solver_pids
        self.solver: Optional[Z3] = None

    def __str__(self) -> str:
        """ Markings to textual format.

        Returns
        -------
        str
            Debugging format.
        """
        text = ""
        for marking in self.markings:
            text += "->"
            for place, tokens in marking.items():
                text += " {}:{}".format(place, tokens)
            text += "\n"
        return text

    def smtlib(self) -> str:
        """ Assert markings (DNF).
        
        Returns
        -------
        str
            SMT-LIB format.
        """
        if not self.markings:
            return ""

        if self.ptnet_reduced is None:
            places = self.ptnet.places
        else:
            places = self.ptnet_reduced.places

        smt_input = "(assert (or "

        for marking in self.markings:
            smt_input += "(and "
            for place, tokens in marking.items():
                smt_input += "(= {} {})".format(place, tokens)
            for place in places:
                if place not in marking:
                    smt_input += "(= {} 0)".format(place)
            smt_input += ")"
        smt_input += "))\n"

        return smt_input

    def parse_markings(self, filename: str) -> None:
        """ Parse markings (.aut file format).

        Parameters
        ----------
        filename : str
            Path to the list of markings (.aut format).
        """
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = line.strip().replace('(', '').replace(')', '').split(',')
                    if len(content) >= 3 and content[0] == content[-1]:
                        content = split(r'\s+', content[1].replace('"', ''))
                        consistent = True
                        marking = dict()
                        for marking_data in content:
                            place_marking = marking_data.split('.')
                            if place_marking[0] != 'S':
                                consistent = False
                                break
                            place_marking = place_marking[1].split('*')
                            place_id = place_marking[0].replace(
                                '`', '').replace('{', '').replace('}', '')
                            if place_id == '':
                                consistent = False
                                break
                            if len(place_marking) > 1:
                                tokens = int(place_marking[1])
                            else:
                                tokens = 1
                            marking[place_id] = tokens
                        if consistent:
                            self.markings.append(marking)
        except FileNotFoundError as e:
            exit(e)

    def prove(self, result: Queue[tuple[Verdict, Marking]], concurrent_pids: Queue[list[int]]) -> None:
        """ Prover.

        Parameters
        ----------
        result : Queue of tuple of Verdict, Marking
            Queue to exchange the verdict.
        concurrent_pids : Queue of int
            Queue to get the PIDs of the concurrent methods.
        """
        info("[ENUMERATIVE] RUNNING")
        self.solver = Z3(debug=self.debug, solver_pids=self.solver_pids)

        if self.ptnet_reduced is None:
            self.prove_without_reduction()
        else:
            self.prove_with_reduction()

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if self.solver.aborted:
            return

        # Put the result in the queue
        verdict, model = Verdict.INV, None
        if self.solver.check_sat():
            verdict = Verdict.CEX
            model = self.solver.get_marking(self.ptnet)
        result.put((verdict, model))

        # Terminate concurrent methods
        send_signal_pids(concurrent_pids.get(), STOP)

    def prove_without_reduction(self) -> None:
        """ Prover for non-reduced Petri net.
        """
        info("[ENUMERATIVE] Declaration of the places")
        self.solver.write(self.ptnet.smtlib_declare_places())
        info("[ENUMERATIVE] Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))
        info("[ENUMERATIVE] Markings")
        self.solver.write(self.smtlib())

    def prove_with_reduction(self) -> None:
        """ Prover for reduced Petri net.
        """
        info("[ENUMERATIVE] Declaration of the places")
        self.solver.write(self.ptnet.smtlib_declare_places())
        info("[ENUMERATIVE] Reduction equations")
        self.solver.write(self.system.smtlib())
        info("[ENUMERATIVE] Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))
        info("[ENUMERATIVE] Markings from the reduced Petri net")
        self.solver.write(self.smtlib())
