"""
Abstract Checker.

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
from multiprocessing import Queue
from typing import Optional

from smpt.exec.utils import Verdict


class AbstractChecker(ABC):
    """ Abstract Checker.
    """

    @abstractmethod
    def prove(self, result: Queue[Verdict], concurrent_pids: Queue[Optional[int]]):
        """ Prover.
        """
        pass
