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
__version__ = "4.0.0"

import logging as log
from multiprocessing import Queue
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.tipx import Tipx
from smpt.interfaces.walk import Walk
from smpt.ptio.ptnet import PetriNet
from smpt.ptio.verdict import Verdict


class RandomWalk(AbstractChecker):
    """ Random walk method.
    """

    def __init__(self, ptnet: PetriNet, formula, shadow_projection: bool = False, tipx: bool = False, debug: bool = False, solver_pids: Optional[Queue[int]] = None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Formula to study
        self.formula = formula

        # Shadow-projection
        self.shadow_projection = shadow_projection

        # Walker
        self.solver = Tipx(ptnet.filename, debug=debug, solver_pids=solver_pids) if tipx else Walk(
            ptnet.filename, debug=debug, solver_pids=solver_pids)

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[RANDOM-WALK] RUNNING")

        log.info("[RANDOM-WALK] Walk")
        formula_filename = self.formula.projection_filename if self.shadow_projection else self.formula.walk_filename
        sat = self.solver.check_sat(formula_filename)

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if not sat or self.solver.aborted:
            return

        # Put the result in the queue
        result.put((Verdict.CEX, None))

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)
