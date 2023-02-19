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

    def __init__(self, ptnet: PetriNet, formula: Formula, ptnet_slicing: Optional[PetriNet] = None, formula_slicing: Optional[Formula] = None, parikh: bool = False, slice: bool = False, timeout: Optional[int] = None, debug: bool = False, solver_pids: Optional[Queue[int]] = None, additional_techniques: Optional[Queue[str]] = None):
        """ Initializer.
        """
        # Initial Petri net and formula
        self.ptnet = ptnet
        self.formula = formula

        # Petri net and formula for slicing
        self.ptnet_slicing = ptnet_slicing
        self.formula_slicing = formula_slicing

        # Parikh
        self.parikh = parikh

        # Slicing
        self.slice = slice

        # Timeout
        self.timeout = int(timeout / 2) if slice and timeout else None

        # Walkers
        if  parikh and self.formula.parikh_filename is not None and getsize(self.formula.parikh_filename) > 0:
            self.solver = Walk(ptnet.filename, parikh_filename=formula.parikh_filename, debug=debug, timeout=self.timeout, solver_pids=solver_pids)
        else:
            self.solver = Walk(ptnet.filename, debug=debug, timeout=self.timeout, solver_pids=solver_pids)
        if slice and self.ptnet_slicing is not None and self.formula_slicing is not None:
            self.solver_slicing = Walk(ptnet_slicing.filename, slice=slice, debug=debug, solver_pids=solver_pids)
        else:
            self.solver_slicing = None

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

        if not sat and self.solver_slicing:
            info("[RANDOM-WALK] Walk slicing")
            sat = self.solver_slicing.check_sat(self.formula_slicing.walk_filename)
            sat = sat and not self.solver_slicing.aborted
            if sat and self.additional_techniques is not None and self.slice:
                self.additional_techniques.put('SLICING')

        # Kill the solver
        self.solver.kill()

        if not sat:
            return

        # Put the result in the queue
        result.put((Verdict.CEX, None))

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)
