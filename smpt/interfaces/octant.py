
"""
Octant Interface

Dependency: https://github.com/nicolasAmat/Octant

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

from itertools import repeat
from multiprocessing.pool import ThreadPool
from subprocess import CalledProcessError, TimeoutExpired, check_output
from typing import TYPE_CHECKING, Optional

if TYPE_CHECKING:
    from smpt.ptio.formula import Formula


def project(ptnet_filename: str, formulas: list[Formula], timeout: int = 3, show_time: bool = False, show_shadow_completeness: bool = False) -> list[tuple[str, bool]]:
    """ Project a list of formulas.

    Parameters
    ----------
    ptnet_filename : str
        A Petri net filename
    formulas : list of Formula
        List of formula to project.
    timeout : int, optional
        Projection timeout.
    show_time : bool, optional
        Show time flag.
    show_shadow_completeness: bool, optional
        Show shadow-completeness flag.

    Returns
    -------
    list of tuple of str, bool
        List of projected formulas and their corresponding shadow-completeness flag.
    """
    pool = ThreadPool(processes=4)
    return pool.starmap(project_helper, zip(repeat(ptnet_filename), formulas, repeat(timeout), repeat(show_time), repeat(show_shadow_completeness)))


def project_helper(ptnet_filename: str, formula: Formula, timeout: int = 3, show_time: bool = False, show_shadow_completeness: bool = False) -> tuple[Optional[str], bool]:
    """ Project a formula (helper).

    Parameters
    ----------
    ptnet_filename : str
        A Petri net filename
    formulas : Formula
        Formula to project.
    timeout : int, optional
        Projection timeout.
    show_time : bool, optional
        Show time flag.
    show_shadow_completeness: bool, optional
        Show shadow-completeness flag.

    Returns
    -------
    list of tuple of str, bool
        Projected formula and its corresponding shadow-completeness flag.
    """
    process = ['octant.exe', 'smt-format', 'load', ptnet_filename]

    if show_time:
        process.append('time')

    if show_time:
        process += ['load-forms', formula.walk_filename, 'project', 'time', 'fprint']
    else:
        process += ['load-forms', formula.walk_filename, 'project', 'fprint']

    try:
        output = check_output(process, timeout=timeout).decode('utf-8').splitlines()
    except (TimeoutExpired, CalledProcessError):
        return (None, False)

    time_information, completeness_information = "", ""

    for line in output:

        if show_time and '# Time:' in line:
            time_information = ' | time: ' + line.split()[-2]

        else:
            split_line = line.split(' # ')
            if len(split_line) < 2:
                return (None, False)

            projected_formula, complementary_data = split_line
            str_completeness, ratio_cubes = complementary_data.split(' ', 1)
            completeness = str_completeness == 'complete'

            if show_shadow_completeness:
                completeness_information = ' | shadow-complete: ' + str(completeness) + ' | ratio: ' + ratio_cubes

            if show_time or show_shadow_completeness:
                print("# Projection of " + formula.identifier + time_information + completeness_information)

            return (projected_formula, completeness)
    return (None, False)
