"""
Utils to Manage Processes

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

import signal
from os import getpgid, getpid, kill, killpg

STOP = signal.SIGTERM
KILL = signal.SIGKILL


def send_signal_pids(pids: list[int], signal_to_send: signal.Signals):
    """ Send a signal to a list of processes
        (except the current process).

    Parameters
    ----------
    pids : list of int
        List of processes.
    signal_to_send : Signals
        Signal to send.
    """
    current_pid = getpid()

    for pid in pids:
        # Do not send a signal to the current process
        if pid == current_pid:
            continue

        try:
            kill(pid, signal_to_send)
        except OSError:
            pass


def send_signal_group_pid(pid: int, signal_to_send: signal.Signals):
    """ Send a signal to the group pid of a given process.
 
    Parameters
    ----------
    pid : int
        Process.
    signal_to_send : Signals
        Signal to send.
    """
    try:
        killpg(getpgid(pid), signal_to_send)
    except (ProcessLookupError, PermissionError):
        pass
