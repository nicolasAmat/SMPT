
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
__version__ = "5.0"

from logging import warning
from multiprocessing import Queue
from os import system
from random import random
from subprocess import PIPE, Popen
from sys import exit
from time import sleep
from typing import Optional

from smpt.exec.utils import KILL, send_signal_pids
from smpt.interfaces.solver import Solver
from smpt.ptio.ptnet import Marking, PetriNet


class Walk(Solver):
    """ Walk interface.

    Note
    ----
    Dependency: https://projects.laas.fr/tina/index.php 

    Attributes
    ----------
    ptnet_filename : str
        A Petri net filename.
    slice : bool
        Slicing mode.
    parikh_filename : str, optional
        Path to an eventual Parikh file.
    solver : Popen, optional
        A walk process.
    timeout : int
        Timeout of walk.
    solver_pids : Queue of int
        Queue of solver pids.
    aborted : bool
        Aborted flag.
    debug : bool
        Debugging flag.
    """

    def __init__(self, ptnet_filename: str, slice: bool = False, parikh_filename: Optional[str] = None, debug: bool = False, timeout: int = 0, solver_pids: Optional[Queue[int]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet_filename : str
            A Petri net filename.
        slice : bool, optional
            Slicing mode.
        parikh_filename : str, optional
            Path to an eventual Parikh file.
        debug: bool, optional
            Debugging flag.
        timeout: int, optional
            Timeout of walk.
        solver_pids : Queue of int, optional
            Queue of solver pids.
        """
        # Petri net
        self.ptnet_filename: str = ptnet_filename

        # Slicing mode
        self.slice: bool = slice

        # Parikh vector
        self.parikh_filename: Optional[str] = parikh_filename

        # Solver
        self.solver: Optional[Popen] = None
        self.timeout: int = timeout
        self.solver_pids: Queue[int] = solver_pids

        # Flags
        self.aborted: bool = False
        self.debug: bool = debug

    def kill(self) -> None:
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal_pids([self.solver.pid], KILL)

    def abort(self) -> None:
        """ Abort the solver.
        """
        warning("Walk process has been aborted")
        self.solver.kill()
        self.aborted = True
        exit()

    def readline(self, debug: bool = False) -> str:
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

    def check_sat(self, walk_filename: str = None, restart_counter: int = 0) -> bool:
        """ Check if a state violates the formula.

        Parameters
        ----------
        walk_filename : str, optional
            Path to the formula (.ltl formula).
        restart_counter : int, optional
            Maximum number of restarting.

        Returns
        -------
        bool
            True if a state violates the formula.

        Raises
        ------
        ValueError
            No filename.
        """
        if restart_counter == 10:
            return False

        if walk_filename is None:
            raise ValueError("Walk: no filename")

        process = ['walk', '-R', '-loop', '-seed', self.ptnet_filename, '-ff', walk_filename]

        if self.parikh_filename:
            process += ['-favor', self.parikh_filename]
        elif self.slice:
            process += ["-reduce", "-rg,redundant,compact+,4ti2", "-redundant-limit", "650", "-redundant-time", "10"]

        if self.timeout:
            process += ['-t', str(self.timeout)]

        if not restart_counter:
            system("sync")

        self.solver = Popen(process, stdout=PIPE, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        self.solver.wait()
        output = self.readline()

        if self.solver.returncode and output != 'FALSE':
            sleep(random())
            return self.check_sat(walk_filename, restart_counter=restart_counter + 1)
        else:
            return not (output != 'FALSE')

    def write(self, input: str, debug: Optional[bool] = None) -> None:
        """ Write instructions.

        Parameters
        ----------
        input : str 
            Input instructions.
        debug : bool
            Debugging flag.

        Raises
        ------
        NotImplementedError
            This methods must not be called.
        """
        raise NotImplementedError

    def get_marking(self, ptnet: PetriNet, k: Optional[int] = None) -> Marking:
        """ Get a marking from the current SAT stack.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.
        k : int, optional
            Order.

        Returns
        -------
        Marking
            Marking from the current stack.

        Raises
        ------
        NotImplementedError
            This method must not be called.
        """
        raise NotImplementedError
