#!/usr/bin/env python3

"""
Utils to manage process.

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
__version__ = "3.0.0"

import os
import signal


RESUME = signal.SIGCONT
STOP = signal.SIGTERM
SUSPEND = signal.SIGSTOP


def send_signal(pids, signal_to_send):
    """ Send a signal to a list of process
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
