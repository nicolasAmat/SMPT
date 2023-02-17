"""
Initial Marking Evaluation

Documentation: https://projects.laas.fr/tina/manuals/walk.html

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

from logging import info
from multiprocessing import Queue
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import PetriNet
from smpt.ptio.verdict import Verdict


class InitialMarking(AbstractChecker):
    """ Initial Marking method.
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, debug: bool = False, solver_pids: Optional[Queue[int]] = None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Formula to study
        self.formula = formula

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[INITIAL-MARKING] RUNNING")
        verdict = Verdict.UNKNOWN

        info("[INITIAL-MARKING] Checking contradiction")
        tautology = self.formula.R_skeleton.tautology()
        if tautology is True:
            verdict = Verdict.CEX
        elif tautology is False:
            verdict = Verdict.INV    

        info("[INITIAL-MARKING] Evaluating")
        if verdict == Verdict.UNKNOWN:
            if not self.formula.R_skeleton.eval(self.ptnet.initial_marking):
                return
            else:
                verdict = Verdict.CEX

        # Put the result in the queue
        result.put((verdict, None))

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)
