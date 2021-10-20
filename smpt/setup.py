#!/usr/bin/env python3

"""
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

from cx_Freeze import setup, Executable

setup(
    name='smpt',
    version='2.0.0',
    description='SMPT - an SMT-based model-checker that takes advantage of nets reduction',
    author='Nicolas AMAT, LAAS-CNRS',
    executables = [Executable("smpt.py")]
)
