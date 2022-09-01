
"""
Abstract Solver

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

from abc import ABC, abstractmethod
from typing import Optional

from smpt.ptio.ptnet import Marking, PetriNet


class Solver(ABC):
    """ Solver abstract class.

        Note
        ----
        Can be: Z3, MiniZinc, Walk
    """

    aborted: bool = False

    @abstractmethod
    def kill(self) -> None:
        """" Kill the process.
        """
        pass

    @abstractmethod
    def abort(self) -> None:
        """ Abort the solver.
        """
        pass

    @abstractmethod
    def write(self, input: str, debug: Optional[bool] = None) -> None:
        """ Write instructions.

        Parameters
        ----------
        input : str 
            Input instructions.
        debug : bool
            Debugging flag.
        """
        pass

    @abstractmethod
    def readline(self, debug: Optional[bool] = False) -> str:
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
        pass

    @abstractmethod
    def check_sat(self) -> Optional[bool]:
        """ Check the satisfiability of the current stack.

        Returns
        -------
        bool, optional
            Satisfiability of the current stack.
        """
        pass

    @abstractmethod
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
        pass
