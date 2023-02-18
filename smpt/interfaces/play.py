
"""
Play Interface

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
__version__ = "5.0"

from subprocess import run


def play(path_ptnet: str, path_trace: str, debug: bool = False) -> bool:
    """ Play a trace.

    Parameters
    ----------
    path_ptnet : str
        Path to the original colored Petri net (.pnml format).
    path_trace : str
        Path to the trace to checK (.scn format).
    debug : bool, optional
        Debugging flag.

    Returns
    -------
    bool
        True if the trace is fireable from the initial marking, false otherwise.
    """
    output = run(['play', path_ptnet], input=bytes("l {}".format(path_trace), 'utf-8'), capture_output=True).stdout

    for line in output.decode('utf-8').splitlines():

        if debug:
            print(line)

        if 'loaded' in line:
            result = True
            break

        if 'error' in line:
            result = False
            break

    return result
