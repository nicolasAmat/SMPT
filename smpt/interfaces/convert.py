
"""
Conversion Interface

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
import tempfile


def convert(path_pnml: str) -> tuple[str, bool]:
    """ Convert .pnml to .net.

    Parameters
    ----------
    path_pnml : str
        Path to the original Petri net (.pnml format).
    path_net : str
        Path to the converted Petri net (.net format).

    Returns
    -------
    tuple of str, bool
        Path to the converted Petri net (.net format) and flag if reduce must use the original file.
    """
    fp_ptnet = tempfile.NamedTemporaryFile(suffix='.net', delete=False)
    use_pnml_reduce = False

    if subprocess.run(["ndrio", path_pnml, fp_ptnet.name], stderr=subprocess.DEVNULL).returncode:
        tina_output = subprocess.run(
            ["tina", "-p", path_pnml], stdout=subprocess.PIPE).stdout.decode('utf-8').splitlines()
        fp_ptnet.writelines("{}\n".format(line).encode()
                            for line in tina_output[10:-5])
        fp_ptnet.flush()
        use_pnml_reduce = True

    return (fp_ptnet.name, use_pnml_reduce)
