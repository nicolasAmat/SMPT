
"""
TiPX Interface

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
from typing import TYPE_CHECKING, Optional

if TYPE_CHECKING:
    from smpt.ptio.formula import Formula

from smpt.exec.utils import KILL, send_signal_pids
from smpt.interfaces.solver import Solver
from smpt.ptio.ptnet import Marking, PetriNet


class Tipx(Solver):
    """ TiPX interface.

    Note
    ----
    Dependency: https://github.com/nicolasAmat/tipx 

    Attributes
    ----------
    ptnet_filename : str
        A Petri net filename.
    solver : Popen, optional
        A TiPX process.
    timeout : int
        Timeout of walk.
    solver_pids : Queue of int
        Queue of solver pids.
    aborted : bool
        Aborted flag.
    debug : bool
        Debugging flag.
    """

    def __init__(self, ptnet_filename: str, debug: bool = False, timeout: int = 0, solver_pids: Optional[Queue[int]] = None) -> None:
        """ Initializer.

        Parameters
        ----------
        ptnet_filename : str
            A Petri net filename
        debug: bool, optional
            Debugging flag.
        timeout: int, optional
            Timeout of walk.
        solver_pids : Queue of int, optional
            Queue of solver pids.
        """
        # Petri net
        self.ptnet_filename: str = ptnet_filename

        # Solver
        self.solver: Optional[Popen] = None
        self.timeout: int = timeout
        self.solver_pids: Queue[int] = solver_pids

        # Flags
        self.debug: bool = debug
        self.aborted = False

    def kill(self) -> None:
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal_pids([self.solver.pid], KILL)

    def abort(self) -> None:
        """ Abort the solver.
        """
        log.warning("Walk process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

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

    def check_sat(self, formula_filename: str = None) -> bool:
        """ Check if a state violates the formula.

        Parameters
        ----------
        formula_filename : str, optional
            Path to the formula (.ltl format).

        Returns
        -------
        bool
            True if a state violates the formula.

        Raises
        ------
        ValueError
            No filename.
        """
        if formula_filename is None:
            raise ValueError("TiPX: no filename")

        process = ['tipx.exe', 'load', self.ptnet_filename,
                   'load-forms', formula_filename]
        if self.timeout:
            process += ['twalk', str(self.timeout)]
        else:
            process.append('walk')

        self.solver = Popen(process, stdout=PIPE, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        line = self.readline()
        while '<+>' not in line:
            line = self.readline()

        return 'Bingo' in line

    def project(self, formulas: list[Formula], show_time: bool = False, show_shadow_completeness: bool = False) -> list[tuple[str, bool]]:
        """ Project a list of formulas.
        
        Parameters
        ----------
        formulas : list of Formula
            List of formula files to project.
        show_time : bool, optional
            Show time flag.
        show_shadow_completeness: bool, optional
            Show shadow-completeness flag.

        Returns
        -------
        list of tuple of str, bool
            List of projected formulas and their corresponding shadow-completeness flag.
        """
        process = ['tipx.exe', 'load', self.ptnet_filename]

        if show_time:
            process.append('time')

        for formula in formulas:
            if show_time:
                process += ['load-forms', formula.walk_filename,
                            'project', 'time', 'fprint']
            else:
                process += ['load-forms',
                            formula.walk_filename, 'project', 'fprint']

        self.solver = Popen(process, stdout=PIPE, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        projected_formulas = []
        counter = 0

        line = self.readline()
        while line:

            if show_time and '# Time:' in line:
                time_information = ' | time: ' + line.split()[-2]
            else:
                projected_formula, str_completeness = line.split(' # ')
                completeness = str_completeness == 'complete'

                if show_shadow_completeness:
                    completeness_information = ' | shadow-completeness: ' + \
                        str(completeness)

                projected_formulas.append((projected_formula, completeness))

                if show_time or show_shadow_completeness:
                    print(
                        "# Projection of " + formulas[counter].identifier + time_information + completeness_information)
                    counter += 1

            line = self.readline()

        return projected_formulas

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
