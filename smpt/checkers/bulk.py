"""
Bulk Meta Method (PDR-REACH-SATURATED (10sec and optional) -> COMPOUND -> WALK)
This method is specific to the Model Checking Contest.

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

from logging import info
from multiprocessing import Process, Queue
from typing import Optional

from smpt.checkers.abstractchecker import AbstractChecker
from smpt.checkers.compound import Compound
from smpt.checkers.pdr import PDR
from smpt.checkers.randomwalk import RandomWalk
from smpt.exec.utils import KILL, STOP, send_signal_group_pid, send_signal_pids
from smpt.interfaces.walk import Walk
from smpt.ptio.formula import Formula, Properties
from smpt.ptio.ptnet import PetriNet


class Bulk(AbstractChecker):
    """
    Bulk meta method.
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, properties: Properties, formula_compound: Formula, pdr: bool = False, slice : bool = False, debug: bool = False, solver_pids: Optional[Queue[int]] = None, bulk_techniques: Optional[Queue[str]] = None):
        """ Initializer.
        """
        # Local queue of solver pids (for PDR)
        self.solver_pids_bis: Queue[int] = Queue() if pdr else None

        # Additional techniques
        self.bulk_techniques = bulk_techniques

        # Methods
        self.pdr = PDR(ptnet, formula, debug=debug, method='REACH', saturation=True, solver_pids=solver_pids, solver_pids_bis=self.solver_pids_bis) if pdr else None
        self.compound = Compound(formula_compound, properties, debug=debug, solver_pids=solver_pids)
        self.walk = RandomWalk(ptnet, formula, slice=slice, debug=debug, solver_pids=solver_pids)

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[BULK] RUNNING")

        # Run PDR (if enabled)
        if self.pdr:
            self.run_helper(self.pdr.prove, 10, ['IMPLICIT', 'SAT-SMT', 'PDR_REACH_SATURATED'], result, concurrent_pids)
            self.pdr = None

        # Run COMPOUND
        self.run_helper(self.compound.prove, None, ['COMPOUND'], result, concurrent_pids)
        self.compound = None

        # Run WALK
        self.run_helper(self.walk.prove, None, ['WALK'], result, concurrent_pids)
        self.walk = None

    def run_helper(self, prover, timeout, techniques, result, concurrent_pids):
        """ Run and manage methods.
        """
        # Remove all bulk techniques
        while not self.bulk_techniques.empty():
            self.bulk_techniques.get()

        # Add new techniques
        for technique in techniques:
            self.bulk_techniques.put(technique)

        # Get pids of concurrent methods
        pids = concurrent_pids.get()

        # Run process
        proc = Process(target=prover, args=(result, concurrent_pids,))
        proc.start()
        proc_id = proc.pid

        # Return pids (by adding the new process)
        concurrent_pids.put(pids + [proc_id])

        proc.join(timeout=timeout)

        # Kill method
        send_signal_pids([proc_id], STOP)

        # Kill local solvers
        if self.solver_pids_bis:
            while not self.solver_pids_bis.empty():
                send_signal_group_pid(self.solver_pids_bis.get(), KILL)
