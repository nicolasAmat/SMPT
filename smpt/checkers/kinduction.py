"""
K-Induction

Based on:
Mary Sheeran, Satnam Singh, and Gunnar Stälmarck.
Checking safety properties using induction and a SAT-solver. 
FMCAD 2000

Adapted for Petri nets

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

import logging as log

from smpt.interfaces.z3 import Z3


class KInduction:
    """
    K-Induction method.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False, induction_queue=None, solver_pids=None):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet

        # Reduced Petri net
        self.ptnet_reduced = ptnet_reduced

        # System of linear equations
        self.system = system

        # Formula to study
        self.formula = formula

        # SMT solver
        self.solver = Z3(debug=debug, solver_pids=solver_pids)

        # Queue shared with BMC
        self.induction_queue = induction_queue

    def smtlib(self, k):
        """ SMT-LIB format for debugging.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction(k)
        else:
            smt_input = self.smtlib_with_reduction(k)

        smt_input += "(check-sat)\n"

        return smt_input

    def smtlib_without_reduction(self, k):
        """ SMT-LIB format for debugging.
            Case without reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net (iteration: 0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        for i in range(k):
            smt_input += "; Assert states safes (iteration:{})\n".format(i)
            smt_input += self.formula.P.smtlib(i, assertion=True)
            
            smt_input += "; Declaration of the places from the Petri net (iteration: {})\n".format(1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet.smtlib_transition_relation(i, eq=False)

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(k, assertion=True)

        return smt_input

    def smtlib_with_reduction(self, k):
        """ SMT-LIB format for debugging.
            Case with reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the initial net (iteration: 0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Assert reduction equations\n"
        smt_input += self.system.smtlib(0, 0)

        for i in range(k):

            smt_input += "; Assert safe states (iteration: {})\n".format(i)
            smt_input += self.formula.P.smtlib(i, assertion=True)

            smt_input += "; Declaration of the places from the initial net (iteration: {})\n".format(i + 1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1)
        
            smt_input += "; Assert reduction equations\n"
            smt_input += self.system.smtlib(i + 1, i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet_reduced.smtlib_transition_relation(i, eq=False)

        smt_input += "; Formula to check the satisfiability (iteration: {})\n".format(k)
        smt_input += self.formula.R.smtlib(k, assertion=True)

        return smt_input

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[K-INDUCTION] RUNNING")

        if self.ptnet_reduced is None:
            iteration = self.prove_without_reduction()
        else:
            iteration = self.prove_with_reduction()

        if not self.solver.aborted and self.induction_queue is not None:
            self.induction_queue.put(iteration)

        # Kill the solver
        self.solver.kill()

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri Net.
        """
        log.info("[K-INDUCTION] > Initialization")

        log.info("[K-INDUCTION] > Declaration of the places from the Petri net (iteration: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        k = 0
        log.info("[K-INDUCTION] > k = 0")

        log.info("[K-INDUCTION] > Push")
        self.solver.push()

        log.info("[K-INDUCTION] > Formula to check the satisfiability (iteration: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        while self.solver.check_sat():

            log.info("[K-INDUCTION] > Pop")
            self.solver.pop()

            log.info("[K-INDUCTION] > Assert states safe (iteration: {})".format(k))
            self.solver.write(self.formula.P.smtlib(k, assertion=True))

            k += 1
            log.info("[K-INDUCTION] > k = {}".format(k))

            log.info("[K-INDUCTION] > Declaration of the places from the Petri net (iteration: {})".format(k))
            self.solver.write(self.ptnet.smtlib_declare_places(k))

            log.info("[K-INDUCTION] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(self.ptnet.smtlib_transition_relation(k - 1, eq=False))

            log.info("[K-INDUCTION] > Push")
            self.solver.push()

            log.info("[K-INDUCTION] > Formula to check the satisfiability (iteration: {})".format(k))
            self.solver.write(self.formula.R.smtlib(k, assertion=True))

        return k

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        log.info("[K-INDUCTION] > Initialization")

        log.info("[K-INDUCTION] > Declaration of the places from the initial net (iteration: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        log.info("[K-INDUCTION] > Assert reduction equations")
        self.solver.write(self.system.smtlib(0, 0))

        log.info("[K-INDUCTION] > Push")
        self.solver.push()

        k = 0
        log.info("[K-INDUCTION] > k = 0")

        log.info("[K-INDUCTION] > Formula to check the satisfiability (iteration: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        while self.solver.check_sat():

            log.info("[K-INDUCTION] > Pop")
            self.solver.pop()

            log.info("[K-INDUCTION] > Assert safe states (iteration: {})".format(k))
            self.solver.write(self.formula.P.smtlib(k, assertion=True))

            k += 1
            log.info("[K-INDUCTION] > k = {}".format(k))

            log.info("[K-INDUCTION] > Declaration of the places from the initial net (iteration: {})".format(k))
            self.solver.write(self.ptnet.smtlib_declare_places(k))

            log.info("[K-INDUCTION] > Assert reduction equations")
            self.solver.write(self.system.smtlib(k, k))

            log.info("[K-INDUCTION] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(self.ptnet_reduced.smtlib_transition_relation(k - 1, eq=False))

            log.info("[K-INDUCTION] > Push")
            self.solver.push()

            log.info("[K-INDUCTION] > Formula to check the satisfiability (iteration: {})".format(k))
            self.solver.write(self.formula.R.smtlib(k, assertion=True))

        return k

