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
import os
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

    def __init__(self, ptnet: PetriNet, formula, tipx: bool = False, parikh_timeout: Optional[int] = None, debug: bool = False, solver_pids: Optional[Queue[int]] = None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Formula to study
        self.formula = formula

        # Timeout for Parikh walking
        self.parikh_timeout = parikh_timeout

        # Walkers
        self.solver = Tipx(ptnet.filename, debug=debug, solver_pids=solver_pids) if tipx else Walk(ptnet.filename, debug=debug, solver_pids=solver_pids)
        if self.parikh_timeout and self.formula.parikh_filename is not None and os.path.getsize(self.formula.parikh_filename) > 0:
            self.solver_parikh = Walk(ptnet.filename, parikh_filename=formula.parikh_filename, debug=debug, timeout=parikh_timeout, solver_pids=solver_pids)
        else:
            self.solver_parikh = None

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[RANDOM-WALK] RUNNING")

        sat = None

        if self.solver_parikh:
            log.info("[RANDOM-WALK] Parikh walk")
            sat = self.solver_parikh.check_sat(self.formula.walk_filename)
            sat = sat and not self.solver_parikh.aborted

        if not sat:
            log.info("[RANDOM-WALK] Walk")
            sat = self.solver.check_sat(self.formula.walk_filename)
            sat = sat and not self.solver.aborted

        # Kill the solver
        self.solver.kill()

        if not sat:
            return

        # Put the result in the queue
        result.put((Verdict.CEX, None))

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)
