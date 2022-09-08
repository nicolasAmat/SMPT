
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

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import subprocess


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
    subprocess.run(["mcc", "smpt", "-i", path_ptnet, '-o',
                   path_ptnet.replace('.pnml', '_unfolded')])
    return path_ptnet.replace('.pnml', '_unfolded.net')
