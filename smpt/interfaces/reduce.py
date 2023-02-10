
"""
Reduce Interface

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

from subprocess import Popen
from time import time


def reduce(path_ptnet: str, path_ptnet_reduced: str, tfg: bool = False, show_time: bool = False):
    """ Reduce Petri net.

    Parameters
    ----------
    path_ptnet : str
        Path to the initial Petri net.
    path_ptnet_reduced : str
        Path to the reduced net.
    tfg : bool
        Only use TFG reductions.
    save_reduced_net : bool
        Save the reduced net. 
    show_time : bool
        Show reduction time.
    """
    option = "-rg,redundant,compact,4ti2" if tfg else "-rg,redundant,compact+,mg,4ti2"

    reduce_start_time = time()

    reduce_process = Popen(["reduce", option, "-redundant-limit", "650", "-redundant-time", "10",
                           "-inv-limit", "1000", "-inv-time", "10", path_ptnet, path_ptnet_reduced], start_new_session=True)

    reduce_process.wait()

    if show_time:
        print("# Reduction time ({}): {}".format("TFG" if tfg else "Full", time() - reduce_start_time))
