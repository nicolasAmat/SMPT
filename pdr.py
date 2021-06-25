#!/usr/bin/env python3

"""
PDR: Property Directed Reachability

Based on "Efficient Implementaiton of Property Directed Reachability", Een et al.
Adapted for "generalized" Petri nets.

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
__version__ = "3.0.0"

import logging as log
import resource
from queue import PriorityQueue

from properties import Atom, IntegerConstant, StateFormula, TokenCount
from solver import Solver
from utils import STOP, send_signal


class PdrSat:
    """ PdrSat.
    """

    def __init__(self, ptnet, formula, debug, F):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet
        # Formula to study
        self.formula = formula

        # SMT solver
        self.solver = Solver(debug)

        # Frames
        self.F = F

    def declare_places(self, init=False):
        """ Declare places.

            If init is True:  declare places at order 0,
            If init is False: declare places at order 0 and 1.
        """
        if init:
            return self.ptnet.smtlib_declare_places(0)
        else:
            return self.ptnet.smtlib_declare_places(0) \
                 + self.ptnet.smtlib_declare_places(1)

    def assert_frame(self, i):
        """ Assert F_i.
        """
        return ''.join(map(lambda x: x.smtlib(0, assertion=True), self.F[i]))

    def unsat_cubes_removal(self):
        """ Remove UNSAT cubes in R.
            If no cubes are satisfiable return True.
        """
        log.info("[PDR] > Remove unsat cubes from R")

        self.solver.reset()
        self.solver.write(self.ptnet.smtlib_declare_places())
        
        if self.formula.R.operator == 'or':
            sat_cubes = []

            for cube in self.formula.R.operands:
                self.solver.push()
                
                self.solver.write(cube.smtlib(assertion=True))
                
                if self.solver.check_sat():
                    sat_cubes.append(cube)
                
                self.solver.pop()

            if not sat_cubes:
                return True

            self.formula.R.operands = sat_cubes
            self.formula.P = StateFormula([self.formula.R], 'not')

        else:
            self.solver.write(self.formula.R.smtlib(assertion=True))

            if not self.solver.check_sat():
                return True

        return False

    def initial_marking_bad_state(self):
        """ sat (I and -P)
        """
        log.info("[PDR] > INIT => P")

        self.solver.write(self.declare_places(init=True))
        self.solver.write(self.ptnet.smtlib_initial_marking(0))
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        return self.solver.check_sat()

    def bad_state(self, k):
        """ sat (F[k] and R) ?
        """
        self.solver.reset()

        self.solver.write(self.declare_places(init=True))
        self.solver.write(self.assert_frame(k))
        self.solver.write(self.formula.R.smtlib(0, assertion=True))

        return self.solver.check_sat()

    def clause_reachable(self, i, c):
        """ sat (Fi and c and T and -c')
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_frame(i))
        self.solver.write(c.smtlib(0, assertion=True))
        self.solver.write(self.ptnet.smtlib_transition_relation(0))
        self.solver.write(c.smtlib(1, assertion=True, negation=True))

        return self.solver.check_sat()

    def state_reachable(self, i, s):
        """ sat (-s and Fi and T and s')
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(s.smtlib(0, assertion=True, negation=True))
        self.solver.write(self.assert_frame(i))
        self.solver.write(self.ptnet.smtlib_transition_relation(0))
        self.solver.write(s.smtlib(1, assertion=True))

        return self.solver.check_sat()

    def witness_generalizer(self, states):
        """ Generalize a witness.
        """
        # Get a marking sequence m_1 -> m_2
        m_1, m_2 = self.solver.get_step(self.ptnet)

        # Get the corresponding fired transition
        tr = self.ptnet.get_transition_from_step(m_1, m_2)

        # Get reached clause (cl in CL(R) s.t. m_2 |= c)
        cube = states.reached_cube(m_2)

        # Return the generalized reached cube according the fired transition
        generalization = cube.generalization(tr)

        log.info("[PDR]   Generalized witness {}".format(generalization))
        return generalization

    def sub_clause_finder_unsat_core(self, i, s):
        """ unsat core (-s and Fi and T and s')
        """
        if isinstance(s, Atom):
            return s.negation()

        self.solver.reset()
        self.solver.enable_unsat_core()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_frame(i))
        self.solver.write(self.ptnet.smtlib_transition_relation(0))
        self.solver.write(s.smtlib(0, assertion=True, negation=True))
        for index, eq in enumerate(s.operands):
            self.solver.write("(assert (! {} :named lit@{}))\n".format(eq.smtlib(1), index))

        unsat_core = self.solver.get_unsat_core()
        inequalities = []
        for index, eq in enumerate(s.operands):
            if "lit@{}".format(index) in unsat_core:
                inequalities.append(eq.negation())
        clause = StateFormula(inequalities, "or")
        log.info("[PDR] \t\t\t>> Clause learned: {}".format(clause))

        return clause


class PDR:
    """ 
    Property Directed Reachability.

    Outline of the execution:
    -------------------------
    Method `pdr_main()` gets a bad state in the last frame and calls`
    rec_block_cube()` to block it, using the helper function `is_blocked()` (
    which checks if a proof-obligation has already been solved) and
    `generalize()` (which shortens a cube). When a property has been proved for
    the last frame, `propagate_blocked_cubes()` pushed cubes of all time-frames
    forward while doing subsumption, handled by `add_blocked_cube`.
    """

    def __init__(self, ptnet, formula, ptnet_reduced=None, system=None, debug=False):
        """ Initializer.
        """
        # Initial Petri net
        self.ptnet = ptnet
        # Formula to study
        self.formula = formula

        # Debug option
        self.debug = debug

        # Blocked cubes of each frame
        self.F = []

        # SMT solver
        self.Z = None
        self.solver = Solver(debug)

    def frames_initialization(self):
        """ Initialization of the frames.
            F0 = I and F1 = T.
        """
        log.info("[PDR] > F[0] = I and F[1] = T")

        # First elem of trace if init formula (F[0] = I)
        equalities = []
        for pl in self.ptnet.places.values():
            equalities.append(Atom(TokenCount([pl]), IntegerConstant(pl.initial_marking), '='))
        self.F.append([StateFormula(equalities, 'and')])

        # Add a new frame to the trace (F1 = T)
        self.F.append([])

    def prove(self, result, concurrent_pids):
        """ Prover.
        """
        log.info("[PDR] RUNNING")

        # Limit the memory of the current thread to 4Go (due to the DNF transform explosion)
        resource.setrlimit(resource.RLIMIT_AS, (4294967296, 4294967296))
        
        self.Z = PdrSat(self.ptnet, self.formula, self.debug, self.F)
        self.solver = self.Z.solver # TODO: manage this in a cleaner way

        # Transform R into DNF
        try:
            self.formula = self.formula.dnf()
        except MemoryError:
            self.solver.kill()
            return

        # Remove UNSAT cubes, and exit if R UNSAT
        if self.Z.unsat_cubes_removal():
            self.exit_helper(True, result, concurrent_pids)
            return True

        log.info("[PDR]   R = {}".format(self.formula.R))
        log.info("[PDR]   P = {}".format(self.formula.P))

        # SAT(I /\ R)?
        if self.Z.initial_marking_bad_state():
            self.exit_helper(False, result, concurrent_pids)
            return False

        pdr_result = self.pdr_main()
        self.exit_helper(pdr_result, result, concurrent_pids)
        return pdr_result

    def pdr_main(self):
        """ Main method.

            Use `rec_block_cube()` to recursively block bad states of the final
            time frame until property holds, then can `propagate_blocked_cubes()`
            to push block cubes from all frames in the trace forward to the
            latest frame where they hold.
        """
        self.frames_initialization()
        k = 1

        while True:
            
            log.info("[PPR] > Blocking phase")
            while self.Z.bad_state(k):

                log.info("[PDR]   k = {}".format(k))

                m = self.Z.solver.get_model_test(self.ptnet, 0)
                c = self.formula.R.reached_cube(m)

                log.info("[PDR]   Bad state c = {} in F[{}]".format(c, k))

                if not self.rec_block(c, k):
                    log.info("[PDR] > Counterexample found")
                    return False

            log.info("[PDR] > Propagation phase")
            k += 1
            
            log.info("[PDR]   F[{}] = T".format(k))
            self.F.append([]) 

            for i in range(1, k):
                for c in self.F[i]:
                    if not self.Z.clause_reachable(i, c):
                        self.F[i+1].append(c)

                if set(self.F[i]) == set(self.F[i + 1]):
                    log.info("[PDR] > Property proved")
                    print("[PDR] > Property proved")
                    return True

    def rec_block(self, s, i):
        """ Recursively block bad states of the final time frame until the
            property holds.
        """
        log.info("[PDR] > RecBlock ({}, {})".format(s, i))

        q = PriorityQueue()
        q.put((i, s))

        while not q.empty():

            i, s = q.get()

            if i == 0:
                log.info("[PDR]   Reached initial state")
                return False

            if self.Z.state_reachable(i - 1, s):
                log.info("[PDR]   {} reachable from F[{}]".format(s, i - 1))
                c = self.Z.witness_generalizer(s)
                q.put((i - 1, c))

            else:
                log.info("[PDR]   Generalize {} to {}".format(s.negation(), i))
                g = self.Z.sub_clause_finder_unsat_core(i - 1, s)
                for j in range(1, i + 1):
                    self.F[j].append(g)

        return True


    # def rec_block(self, s, i):
    #     """ Recursively block bad states of the final time frame until the
    #         property holds.
    #     """
    #     log.info("[PDR] > RecBlock ({}, {})".format(s, i))

    #     if i == 0:
    #         log.info("[PDR]   Reached initial state")
    #         return False

    #     while self.Z.state_reachable(i - 1, s):
    #         log.info("[PDR]   {} reachable from F[{}]".format(s, i - 1))
    #         c = self.Z.witness_generalizer(s)
    #         if not self.rec_block(c, i - 1):
    #             return False

    #     log.info("[PDR]   Generalize {} to {}".format(s.negation(), i))
    #     g = self.Z.sub_clause_finder_unsat_core(i - 1, s)
    #     for j in range(1, i + 1):
    #         self.F[j].append(g)
        
    #     return True

    def exit_helper(self, result, result_output, concurrent_pids):
        """ Helper function to put the result to the output queue,
            and stop the concurrent method if there is one.
        """
        # Kill the solver
        self.solver.kill()

        # Quit if the solver has aborted
        if self.solver.aborted:
            return

        # Put the result in the queue
        result_output.put([not result, None])

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal(concurrent_pids.get(), STOP)

