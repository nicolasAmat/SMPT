"""
BMC: Bounded Model Checking

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

from solver import Z3
from utils import STOP, Verdict, send_signal_pids


class BMC:
    """
    Bounded Model Checking method.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, show_model=False, debug=False, induction_queue=None, solver_pids=None):
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

        # Queue shared with K-Induction
        self.induction_queue = induction_queue

        # Show model option
        self.show_model = show_model

        # SMT solver
        self.solver = Z3(debug=debug, solver_pids=solver_pids)

    def smtlib(self, k):
        """ SMT-LIB format for understanding.
        """
        if self.ptnet_reduced is None:
            smt_input = self.smtlib_without_reduction(k)
        else:
            smt_input = self.smtlib_with_reduction(k)

        smt_input += "; Check satisfiability\n"
        smt_input += "(check-sat)\n"

        return smt_input

    def smtlib_without_reduction(self, k):
        """ SMT-LIB format for understanding.
            Case without reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the Petri net (order: 0)\n"
        smt_input += self.ptnet.smtlib_declare_places(0)

        smt_input += "; Initial marking of the Petri net\n"
        smt_input += self.ptnet.smtlib_initial_marking(0)

        for i in range(k):
            smt_input += "; Declaration of the places from the Petri net (order: {})\n".format(i + 1)
            smt_input += self.ptnet.smtlib_declare_places(i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet.smtlib_transition_relation(i, eq=False)

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(k + 1, assertion=True)

        return smt_input

    def smtlib_with_reduction(self, k):
        """ SMT-LIB format for understanding.
            Case with reduction.
        """
        smt_input = ""

        smt_input += "; Declaration of the places from the initial Petri net\n"
        smt_input += self.ptnet.smtlib_declare_places()

        smt_input += "; Declaration of the additional variables\n"
        smt_input += self.system.smtlib_declare_additional_variables()

        smt_input += "; Formula to check the satisfiability\n"
        smt_input += self.formula.R.smtlib(assertion=True)

        smt_input += "; Reduction equations (not involving places from the reduced Petri net)"
        smt_input += self.system.smtlib_equations_without_places_from_reduced_net()

        smt_input += "; Declaration of the places from the reduced Petri net (order: 0)\n"
        smt_input += self.ptnet_reduced.smtlib_declare_places(0)

        smt_input += "; Initial marking of the reduced Petri net\n"
        smt_input += self.ptnet_reduced.smtlib_initial_marking(0)

        for i in range(k):
            smt_input += "; Declaration of the places from the reduced Petri net (order: {})\n".format(1)
            smt_input += self.ptnet_reduced.smtlib_declare_places(i + 1)

            smt_input += "; Transition relation: {} -> {}\n".format(i, i + 1)
            smt_input += self.ptnet_reduced.smtlib_transition_relation(i, eq=False)

        smt_input += "; Reduction equations\n"
        smt_input += self.system.smtlib_equations_with_places_from_reduced_net(k)

        smt_input += "; Link initial and reduced Petri nets\n"
        smt_input += self.system.smtlib_link_nets(k)

        return smt_input

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[BMC] RUNNING")

        if self.ptnet_reduced is None:
            order = self.prove_without_reduction()
        else:
            order = self.prove_with_reduction()

        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if self.solver.aborted:
            return

        # Put the result in the queue
        model = None
        if order == -1:
            verdict = Verdict.INV
        else:
            verdict = Verdict.CEX
            if self.show_model:
                model = self.solver.get_marking(self.ptnet, order)
        result.put([verdict, model])

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal_pids(concurrent_pids.get(), STOP)

    def prove_without_reduction(self):
        """ Prover for non-reduced Petri Net.
        """
        log.info("[BMC] > Initialization")

        log.info("[BMC] > Declaration of the places from the Petri net (order: 0)")
        self.solver.write(self.ptnet.smtlib_declare_places(0))

        log.info("[BMC] > Initial marking of the Petri net")
        self.solver.write(self.ptnet.smtlib_initial_marking(0))

        log.info("[BMC] > Push")
        self.solver.push()

        log.info("[BMC] > Formula to check the satisfiability (order: 0)")
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        k, k_induction_iteration = 0, float('inf')

        while not self.solver.check_sat():

            if self.induction_queue is not None and not self.induction_queue.empty():
                k_induction_iteration = self.induction_queue.get()

            if k >= k_induction_iteration:
                return -1

            log.info("[BMC] > Pop")
            self.solver.pop()

            k += 1
            log.info("[BMC] > k = {}".format(k))

            log.info("[BMC] > Declaration of the places from the Petri net (order: {})".format(k))
            self.solver.write(self.ptnet.smtlib_declare_places(k))

            log.info("[BMC] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(self.ptnet.smtlib_transition_relation(k - 1, eq=False))

            log.info("[BMC] > Push")
            self.solver.push()

            log.info("[BMC] > Formula to check the satisfiability (order: {})".format(k))
            self.solver.write(self.formula.R.smtlib(k, assertion=True))

        return k

    def prove_with_reduction(self):
        """ Prover for reduced Petri Net.
        """
        log.info("[BMC] > Initialization")

        log.info("[BMC] > Declaration of the places from the initial Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())

        log.info("[BMC] > Declaration of the additional variables")
        self.solver.write(self.system.smtlib_declare_additional_variables())

        log.info("[BMC] > Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        log.info("[BMC] > Reduction equations (not involving places from the reduced Petri net)")
        self.solver.write(self.system.smtlib_equations_without_places_from_reduced_net())

        log.info("[BMC] > Declaration of the places from the reduced Petri net (order: 0)")
        self.solver.write(self.ptnet_reduced.smtlib_declare_places(0))

        log.info("[BMC] > Initial marking of the reduced Petri net")
        self.solver.write(self.ptnet_reduced.smtlib_initial_marking(0))

        log.info("[BMC] > Push")
        self.solver.push()

        log.info("[BMC] > Reduction equations")
        self.solver.write(self.system.smtlib_equations_with_places_from_reduced_net(0))

        log.info("[BMC] > Link initial and reduced Petri nets")
        self.solver.write(self.system.smtlib_link_nets(0))

        if not self.ptnet_reduced.places and not self.solver.check_sat():
            return -1

        k, k_induction_iteration = 0, float('inf')

        while not self.solver.check_sat():

            if self.induction_queue is not None and not self.induction_queue.empty():
                k_induction_iteration = self.induction_queue.get()

            if k >= k_induction_iteration:
                return -1

            log.info("[BMC] > Pop")
            self.solver.pop()

            k += 1
            log.info("[BMC] > k = {}".format(k))

            log.info("[BMC] > Declaration of the places from the reduced Petri net (order: {})".format(k))
            self.solver.write(self.ptnet_reduced.smtlib_declare_places(k))

            log.info("[BMC] > Transition relation: {} -> {}".format(k - 1, k))
            self.solver.write(self.ptnet_reduced.smtlib_transition_relation(k - 1, eq=False))

            log.info("[BMC] > Push")
            self.solver.push()

            log.info("[BMC] > Reduction equations")
            self.solver.write(self.system.smtlib_equations_with_places_from_reduced_net(k))

            log.info("[BMC] > Link initial and reduced Petri nets")
            self.solver.write(self.system.smtlib_link_nets(k))

        return k

