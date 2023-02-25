"""
Random Walk

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
__version__ = "5.0"

from logging import info
from multiprocessing import Queue
from os.path import getsize
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.walk import Walk
from smpt.ptio.formula import Formula
from smpt.ptio.ptnet import PetriNet
from smpt.ptio.verdict import Verdict


class RandomWalk(AbstractChecker):
    """ Random walk method.
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, parikh: bool = False, slice: bool = False, debug: bool = False, solver_pids: Optional[Queue[int]] = None, additional_techniques: Optional[Queue[str]] = None):
        """ Initializer.
        """
        # Initial Petri net and formula
        self.ptnet = ptnet
        self.formula = formula

        # Parikh
        self.parikh = parikh and self.formula.parikh_filename is not None and getsize(self.formula.parikh_filename) > 0

        # Slicing
        self.slice = not self.parikh and slice

        # Walkers
        if self.parikh:
            self.solver = Walk(ptnet.filename, parikh_filename=formula.parikh_filename, debug=debug, solver_pids=solver_pids)
        elif self.slice:
            self.solver = Walk(ptnet.filename, slice=slice, debug=debug, solver_pids=solver_pids)
        else:
            self.solver = Walk(ptnet.filename, debug=debug, solver_pids=solver_pids)

        # Additional techniques queue
        self.additional_techniques = additional_techniques

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[RANDOM-WALK] RUNNING")

        sat = None

        if self.parikh:
            info("[RANDOM-WALK] Parikh walk")
        else:
            info("[RANDOM-WALK] Walk")
        sat = self.solver.check_sat(self.formula.walk_filename)
        sat = sat and not self.solver.aborted
        if sat and self.parikh and self.additional_techniques is not None:
            self.additional_techniques.put('PARIKH')
        if sat and self.slice and self.additional_techniques is not None:
            self.additional_techniques.put('SLICING')

        # Kill the solver
        self.solver.kill()

        if not sat:
            return

        # Put the result in the queue
        result.put((Verdict.CEX, None))

        # Terminate concurrent methods
        send_signal_pids(concurrent_pids.get(), STOP)
