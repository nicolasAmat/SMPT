"""
Bulk Meta Method (PDR-REACH-SATURATED (10sec and optional) -> COMPOUND -> WALK)

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

from smpt.checkers.randomwalk import RandomWalk
from smpt.checkers.abstractchecker import AbstractChecker
from smpt.checkers.compound import Compound
from smpt.checkers.pdr import PDR
from smpt.exec.utils import KILL, STOP, send_signal_group_pid, send_signal_pids
from smpt.interfaces.walk import Walk
from smpt.ptio.formula import Formula, Properties
from smpt.ptio.ptnet import PetriNet


class Bulk(AbstractChecker):
    """
    Bulk meta method.
    """

    def __init__(self, ptnet: PetriNet, formula: Formula, properties: Properties, pdr: bool = False, debug: bool = False, solver_pids: Optional[Queue[int]] = None, additional_techniques: Optional[Queue[str]] = None):
        """ Initializer.
        """
        # Petri net
        self.ptnet = ptnet

        # Formula
        self.formula = formula

        # Properties context
        self.properties = properties

        # Additional techniques
        self.additional_techniques = additional_techniques

        # Local queue of solver pids (for PDR)
        self.solver_pids_bis = Queue() if pdr else None

        # Methods
        self.pdr = PDR(ptnet, formula, debug=debug, method='REACH', saturation=True, solver_pids=solver_pids, solver_pids_bis=self.solver_pids_bis) if pdr else None
        self.compound = Compound(properties.ptnet, formula, properties, debug=debug, solver_pids=solver_pids, solver_pids_bis=self.solver_pids_bis)
        self.walk = RandomWalk(ptnet, formula, debug=debug, solver_pids=solver_pids, solver_pids_bis=self.solver_pids_bis)

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        info("[BULK] RUNNING")

        found_verdict = False

        if self.pdr:
            found_verdict = self.run_helper(self.pdr.prove, 20, ['IMPLICIT', 'SAT-SMT', 'PDR_REACH_SATURATED'], result, concurrent_pids)

        if not found_verdict:
            found_verdict = self.run_helper(self.compound.prove, None, ['COMPOUND'], result, concurrent_pids)

        if not found_verdict:
            self.run_helper(self.walk.prove, None, ['WALK'], result, concurrent_pids)
        
    def run_helper(self, prover, timeout, techniques, result, concurrent_pids):
        """ Run and manage methods.
        """
        found_verdict = False

        local_result = Queue()
        local_concurrent_pids = Queue()

        # Run process
        proc = Process(target=prover, args=(local_result, local_concurrent_pids,))
        proc.start()
        proc_id = proc.pid
        proc.join(timeout=timeout)

        # Check if there is some result
        if not local_result.empty():

            # Found a verdict
            found_verdict = True
            
            # Add additional techniques
            for technique in techniques:
                self.additional_techniques.put(technique)
        
            # Transfer the result
            result.put(local_result.get())

            # Terminate concurrent methods
            if not concurrent_pids.empty():
                send_signal_pids(concurrent_pids.get(), STOP)

        # Kill method
        send_signal_pids([proc_id], KILL)

        # Kill local solvers
        while not self.solver_pids_bis.empty():
            send_signal_group_pid(self.solver_pids_bis.get(), KILL)

        return found_verdict
