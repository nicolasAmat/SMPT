
"""
MiniZinc Interface

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
from subprocess import DEVNULL, PIPE, Popen
from sys import exit
from tempfile import NamedTemporaryFile, _TemporaryFileWrapper
from typing import Optional

from smpt.exec.utils import STOP, send_signal_pids
from smpt.interfaces.solver import Solver
from smpt.ptio.ptnet import Marking, PetriNet, Place


class MiniZinc(Solver):
    """ MiniZinc interface.

    Note
    ----
    Dependency: https://www.minizinc.org/software.html

    Attributes
    ----------
    file : tempfile._TemporaryFileWrapper
        Query file (.mzn format).
    solver : Popen; optional
        A MiniZinc process.
    solver_pids : Queue of int
        Queue of solver pids.
    aborted : bool
        Aborted flag.
    debug : bool
        Debugging flag.
    timeout : int
        Timeout of miniZinc.
    first_line : str
        First line read from the solver.
    """

    def __init__(self, debug: bool = False, timeout: int = 0, solver_pids: Queue[int] = None) -> None:
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
        # File to write formula
        self.file: _TemporaryFileWrapper[str] = NamedTemporaryFile('w', suffix='.mzn')

        # Solver
        self.solver: Optional[Popen] = None
        self.solver_pids: Queue[int] = solver_pids

        # Flags
        self.aborted: bool = False
        self.debug: bool = debug
        self.timeout: int = timeout

        # Set integer bound
        self.write("int: MAX = 1000000;\n")

        self.first_line: str = ""

    def kill(self) -> None:
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal_pids([self.solver.pid], STOP)

    def abort(self) -> None:
        """ Abort the solver.
        """
        warning("MiniZinc process has been aborted")
        self.solver.kill()
        self.aborted = True
        exit()

    def write(self, input: str, debug: bool = False) -> None:
        """ Write instructions into the standard input.

        Parameters
        ----------
        input : str 
            Input instructions.
        debug : bool
            Debugging flag.
        """
        if self.debug or debug:
            print(input)

        self.file.write(input)
        self.file.flush()

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
        if self.solver is None:
            self.abort()

        try:
            minizinc_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(minizinc_output)

        return minizinc_output

    def check_sat(self) -> Optional[bool]:
        """ Check the satisfiability of the current stack.

        Returns
        -------
        bool, optional
            Satisfiability of the current stack.
        """
        self.write("solve satisfy;\n")

        process = ['minizinc', self.file.name]
        if self.timeout:
            process.extend(['--time-limit', str(self.timeout * 1000)])
        self.solver = Popen(process, stdout=PIPE,
                            stderr=DEVNULL, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        minizinc_output = self.readline()
        self.first_line = minizinc_output

        if self.debug:
            print(minizinc_output)

        if minizinc_output in ["=====ERROR=====", "=====UNKNOWN====="]:
            self.abort()
            return None
        else:
            return minizinc_output != "=====UNSATISFIABLE====="

    def get_marking(self, ptnet: PetriNet, k: Optional[int] = None) -> Marking:
        """ Get a marking from the current stack.

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
        """
        marking: dict[Place, int] = {}
        line = self.first_line

        while line and line != '----------':
            place_content = line.split(' = ')

            if len(place_content) < 2:
                break

            self.parse_value(ptnet, place_content, marking)

            line = self.readline()

        return Marking(marking)

    def parse_value(self, ptnet: PetriNet, place_content: list[str], marking: dict[Place, int]) -> None:
        """ Parse a place from the model.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.
        place_content : list of str
            Content to parse.
        marking : dict of Place, int
            Current marking.
        """
        place_marking = int(place_content[1].replace(';', ''))
        place = place_content[0]

        if place_marking and place in ptnet.places:
            marking[ptnet.places[place]] = place_marking
