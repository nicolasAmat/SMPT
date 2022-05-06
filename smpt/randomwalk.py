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

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import logging as log

from solver import Walk
from utils import STOP, Verdict, send_signal_pids


class RandomWalk:
    """ Random walk method.
    """

    def __init__(self, ptnet, formula, debug=False, solver_pids=None, tempfiles_queue=None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Formula to study
        self.formula = formula

        # Walker
        self.solver = Walk(ptnet, debug=debug, solver_pids=solver_pids, tempfiles_queue=tempfiles_queue)

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[RANDOM-WALK] RUNNING")

        log.info("[RANDOM-WALK] Write formula")
        self.solver.write(self.formula.R.walk(assertion=True))

        log.info("[RANDOM-WALK] Walk")
        sat = self.solver.check_sat()

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if not sat or self.solver.aborted:
            return

        # Put the result in the queue 
        result.put([Verdict.CEX, None])

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)

