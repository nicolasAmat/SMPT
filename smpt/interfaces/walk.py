
"""
Walk Interface

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
import sys
from multiprocessing import Queue
from subprocess import PIPE, Popen
from typing import Optional

from smpt.exec.utils import KILL, send_signal_pids
from smpt.interfaces.solver import Solver
from smpt.ptio.ptnet import PetriNet


class Walk(Solver):
    """ Walk interface.
    """

    def __init__(self, ptnet, debug=False, timeout=0, solver_pids=None):
        """ Initializer.
        """
        # Petri net
        self.ptnet: PetriNet = ptnet

        # Solver
        self.solver: Optional[Popen] = None
        self.timeout: int = timeout
        self.solver_pids: Queue[int] = solver_pids

        # Flags
        self.debug: bool = debug
        self.aborted: bool = False

    def kill(self):
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal_pids([self.solver.pid], KILL)

    def abort(self):
        """ Abort the solver.
        """
        log.warning("Walk process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

    def readline(self, debug=False):
        """ Readline from walk.
        """
        try:
            output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(output)

        return output

    def check_sat(self, walk_filename):
        """ Check if a state violates the formula.
        """
        process = ['walk', '-R', '-loop', '-seed',
                   self.ptnet.filename, '-ff', walk_filename]
        if self.timeout:
            process += ['-t', str(self.timeout)]
        self.solver = Popen(process, stdout=PIPE, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        return not (self.readline() != 'FALSE')

    def write(self):
        """ Write instructions.

        Raises
        ------
        NotImplementedError
            This methods must not be called.
        """
        raise NotImplementedError

    def get_marking(self):
        """ Get a marking from the current SAT stack.

        Raises
        ------
        NotImplementedError
            This method must not be called.
        """
        raise NotImplementedError
