
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
__version__ = "4.0.0"

import subprocess
from multiprocessing import Process
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
    unfold_proc = Process(target=unfold, args=(path_ptnet,))
    unfold_proc.start()

    skeleton_proc = Process(target=skeleton, args=(path_ptnet,))
    skeleton_proc.start()

    unfold_proc.join(timeout=0)
    skeleton_proc.join()

    if unfold_proc.is_alive:
        unfold_proc.kill()
        unfold_path = None
    else:
        unfold_path = path_ptnet.replace('.pnml', '_unfolded.net')

    return (unfold_path, path_ptnet.replace('.pnml', '_skeleton.net'))


def unfold(path_ptnet: str) -> str:
    """ Unfold colored Petri net.

    Parameters
    ----------
    path_ptnet : str
        Path to the original colored Petri net (.pnml format).
    
    Returns
    -------
    str
        Path to the unfold Petri net (.net format).
    """
    new_filename = path_ptnet.replace('.pnml', '_unfolded')
    subprocess.run(["mcc", "smpt", "-i", path_ptnet, '-o', new_filename])
    return new_filename + '.net'


def skeleton(path_ptnet: str) -> str:
    """ Compute the skeleton of a colored Petri net.

    Parameters
    ----------
    path_ptnet : str
        Path to the original colored Petri net (.pnml format).
    
    Returns
    -------
    str
        Path to the skeleton (.net format).
    """
    new_filename = path_ptnet.replace('.pnml', '_skeleton')
    subprocess.run(["mcc", "skeleton", "-i", path_ptnet, '-o', new_filename])
    return new_filename + '.net'
