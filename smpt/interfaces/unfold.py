
"""
Unfolding Interface

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

from multiprocessing.pool import ThreadPool
from subprocess import DEVNULL, CalledProcessError, check_output, TimeoutExpired
from typing import Optional


def unfold_and_skeleton(path_ptnet: str, timeout_unfold: Optional[int] = None) -> tuple[Optional[str], str]:
    """ Unfold and compute the skeleton of a colored Petri net.

    Parameters
    ----------
    path_ptnet : str
        Path to the original colored Petri net (.pnml format).
    
    Returns
    -------
    tuple of str, str
        Path to the unfold and skeleton Petri nets (.net format).
    """
    pool = ThreadPool(processes=2)
    result = pool.map(lambda func: func(path_ptnet, timeout_unfold), [unfold, skeleton])
    return result[0], result[1]


def unfold(path_ptnet: str, timeout: Optional[int] = None) -> str:
    """ Unfold colored Petri net.

    Parameters
    ----------
    path_ptnet : str
        Path to the original colored Petri net (.pnml format).
    timeout : int, optional
        Time limit.
    
    Returns
    -------
    str
        Path to the unfold Petri net (.net format).
    """
    new_filename = path_ptnet.replace('.pnml', '_unfolded')
    try:
        check_output('export GOMEMLIMIT="12000000KiB"; ulimit -Sv 12000000 ; mcc smpt -i {} -o {}'.format(path_ptnet, new_filename), timeout=timeout, stderr=DEVNULL, shell=True)
    except (TimeoutExpired, CalledProcessError):
        return None
    return new_filename + '.net'


def skeleton(path_ptnet: str, timeout: Optional[int] = None) -> str:
    """ Compute the skeleton of a colored Petri net.

    Parameters
    ----------
    path_ptnet : str
        Path to the original colored Petri net (.pnml format).
    timeout : int, optional
        Not used.
    
    Returns
    -------
    str
        Path to the skeleton (.net format).
    """
    new_filename = path_ptnet.replace('.pnml', '_skeleton')
    check_output(["mcc", "skeleton", "-i", path_ptnet, '-o', new_filename])
    return new_filename + '.net'
