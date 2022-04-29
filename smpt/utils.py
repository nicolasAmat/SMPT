#!/usr/bin/env python3

"""
Utils to manage processes and verdicts

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

import os
import signal
from enum import Enum

STOP = signal.SIGTERM
KILL = signal.SIGKILL

PRE_TIMEOUT = 30


class Verdict(Enum):
    """ Verdict enum
        INV -> P invariant (R not reachable)
        CEX -> R reachable (P not invariant)
        UNKNOWN
    """
    INV = 1 
    CEX = 2
    UNKNOWN = 3


def worker(parallelizer):
    """ Call run method n parallelizer object.
    """
    return parallelizer.run(PRE_TIMEOUT)


def send_signal_pids(pids, signal_to_send):
    """ Send a signal to a list of processes
        (except the current process).
    """
    current_pid = os.getpid()

    for pid in pids:
        # Do not send a signal to the current process
        if pid == current_pid:
            continue

        try:
            os.kill(pid, signal_to_send)
        except OSError:
            pass


def send_signal_group_pid(pid, signal_to_send):
    """ Send a signal to the group pid of a given process.
    """
    try:
        os.killpg(os.getpgid(pid), signal_to_send)
    except ProcessLookupError:
        pass

