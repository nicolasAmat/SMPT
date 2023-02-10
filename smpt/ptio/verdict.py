"""
Verdict Module

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

from enum import Enum
from signal import SIGKILL, SIGTERM

STOP = SIGTERM
KILL = SIGKILL


class Verdict(Enum):
    """ Verdict enum.

        Note
        ----
        INV -> P invariant (R not reachable)
        CEX -> R reachable (P not invariant)
        UNKNOWN
    """
    INV = 1
    CEX = 2
    UNKNOWN = 3
