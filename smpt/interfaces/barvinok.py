
"""
Barvinok Interface

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


class Barvinok:
    """ Barvinok interface.

    Note
    ----
    Dependency: https://repo.or.cz/barvinok.git

    Attributes
    ----------
    solver : Popen
        A Barvinok process.
    debug : bool
        Debugging flag.
    """

    def __init__(self, debug: bool = False, timeout: int = 0, solver_pids: Queue = None) -> None:
        """ Initializer.

        Parameters
        ----------
        debug : bool, optional
            Debugging flag.
        timeout : int, optional
            Timeout of the solver.
        solver_pids : Queue of int, optional
            Queue of solver pids.
        """
        # Solver
        process = ['z3', '-in']
        if timeout:
            process.append('-T:{}'.format(timeout))
        self.solver: Popen = Popen(process, stdin=PIPE,
                                   stdout=PIPE, start_new_session=True)

        if solver_pids is not None:
            solver_pids.put(self.solver.pid)

        # Flags
        self.aborted: bool = False
        self.debug: bool = debug

    def kill(self) -> None:
        """" Kill the process.
        """
        self.solver.kill()

    def abort(self) -> None:
        """ Abort the solver.
        """
        log.warning("z3 process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

    def write(self, input: str, debug: bool = False) -> None:
        """ Write instructions to the standard input.

        Parameters
        ----------
        input : str 
            Input instructions.
        debug : bool
            Debugging flag.
        """
        if self.debug or debug:
            print(input)

        if input != "":
            try:
                self.solver.stdin.write(bytes(input, 'utf-8'))
            except BrokenPipeError:
                self.abort()

    def flush(self) -> None:
        """ Flush the standard input.
        """
        try:
            self.solver.stdin.flush()
        except BrokenPipeError:
            self.abort()

    def readline(self, debug: bool = False):
        """ Read a line from the standard output.

        Parameters
        ----------
        debug : bool, optional
            Debugging flag.

        Returns
        -------
        str
            Line read.
        """
        try:
            output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(output)

        return output
