#!/usr/bin/env python3

"""
IC3:
Incremental Construction of
Inductive Clauses for Indubitable Correctness

Based on "SAT-Based Model Checking without Unrolling"
Aaron Bradley, VMCAI 2011
Adapted for Petri Net

Indications for orders:
- Case non-reduced:
    pn : 0
    pn': 1
- Case reduced:
    pn : 10     pn_reduced : 0
    pn': 11     pn_reduced': 1   
"""

from pn import PetriNet
from formula import Formula, Clause, Inequality
from eq import System
from solver import Solver

import copy
import logging as log
from subprocess import PIPE, Popen
import sys


class Counterexample(Exception):
    """
    Exception raised in case of a counter-example
    """


class IC3:
    """
    IC3 Method
    """
    def __init__(self, pn, formula, pn_reduced=None, eq=None, debug=False, unsat_core=True):
        """ IC3 initializer.
        """
        self.pn = pn
        self.formula = formula
        self.pn_reduced = pn_reduced
        self.eq = eq

        self.reduced = pn_reduced is not None
        self.pn_current = self.pn_reduced if self.reduced else self.pn

        self.P = None
        self.oars = [] # list of CNF
        self.solver = Solver(debug)

        if unsat_core:
            self.sub_clause_finder = self.sub_clause_finder_unsat_core
        else:
            self.sub_clause_finder = self.sub_clause_finder_mic

    def declare_places(self, init=False):
        """ Declare places.

            If init is True:  declare places at order 0,
            If init is False: declare places at order 0 and 1.
        """
        if init:
            if self.reduced:
                return self.pn.smtlib_declare_places(10)        \
                     + self.pn_reduced.smtlib_declare_places(0)
            else:
                return self.pn.smtlib_declare_places(0)
        else:
            if self.reduced:
                return self.pn.smtlib_declare_places(10)        \
                     + self.pn.smtlib_declare_places(11)        \
                     + self.pn_reduced.smtlib_declare_places(0) \
                     + self.pn_reduced.smtlib_declare_places(1)
            else:
                return self.pn.smtlib_declare_places(0) \
                     + self.pn.smtlib_declare_places(1)

    def assert_equations(self, init=False):
        """ Reduction equations.

            If init is True:  equations at order 0,
            If init is False: equations at order 0 and 1.
        """
        if not self.reduced:
            return ""

        if init:
            return self.eq.smtlib_only_non_reduced_places(10) \
                 + self.eq.smtlib_ordered(0, 10)
        else:
            return self.eq.smtlib_only_non_reduced_places(10) \
                 + self.eq.smtlib_ordered(0, 10)              \
                 + self.eq.smtlib_only_non_reduced_places(11) \
                 + self.eq.smtlib_ordered(1, 11)
    
    def assert_formula(self, i):
        """ F_i
        """
        if i == 0:
            smt_input = self.oars[i][0].smtlib(0, write_assert=True)
        else:
            smt_input = self.oars[i][0].smtlib(self.reduced * 10, write_assert=True)
        for clause in self.oars[i][1:]:
           smt_input += clause.smtlib(0, write_assert=True)
        return smt_input

    def oars_initialization(self):
        """ Initialization of the OARS.
            F0 = I and F1 = P.
        """
        log.info("> F0 = I and F1 = P")
        
        # F0 = I
        inequalities = []
        for pl in self.pn_current.places.values():
            inequalities.append(Inequality(pl, pl.marking, '='))
        self.oars.append([Clause(inequalities, 'and')])
        
        # F1 = P
        inequalities = []
        for ineq in self.formula.clauses:
            inequalities.append(Inequality(ineq.left_member, ineq.right_member, '<'))
        self.P = Clause(inequalities, 'or')
        self.oars.append([self.P])

    def init_marking_reach_bad_state(self):
        """ sat (I and -P)
        """
        log.info("> INIT => P")

        self.solver.write(self.declare_places(init=True))
        self.solver.write(self.assert_equations(init=True))
        self.solver.write(self.pn_current.smtlib_set_marking(0))
        self.solver.write(self.formula.smtlib(self.reduced * 10))
        
        return self.solver.check_sat()

    def init_tr_reach_bad_state(self):
        """ sat (I and T and -P)
        """
        log.info("> INIT and T => P")

        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.pn_current.smtlib_set_marking(0))
        self.solver.write(self.pn_current.smtlib_transitions(0))
        self.solver.write(self.assert_equations())
        self.solver.write(self.formula.smtlib(self.reduced * 10 + 1))

        return self.solver.check_sat()

    def formula_reach_bad_state(self, k):
        """ sat (Fk and T and -P)
        """
        self.solver.reset()
        
        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(k))
        self.solver.write(self.pn_current.smtlib_transitions(0))
        self.solver.write(self.assert_equations())
        self.solver.write(self.formula.smtlib(self.reduced * 10 + 1))
        
        return self.solver.check_sat()

    def formula_reach_clause(self, i, c):
        """ sat (Fi and T and -c)
        """
        self.solver.reset()

        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.pn_current.smtlib_transitions(0))
        self.solver.write(c.smtlib(1, write_assert=True, neg=True))
        
        return self.solver.check_sat()

    def state_reachable(self, i, s):
        """ sat (-s and Fi and T and s')
        """
        self.solver.reset()
        
        self.solver.write(self.declare_places())
        self.solver.write(s.smtlib(0, write_assert=True, neg=True))
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.pn_current.smtlib_transitions(0))
        self.solver.write(self.assert_equations())
        self.solver.write(s.smtlib(1, write_assert=True))
        
        return self.solver.check_sat()

    def formula_reach_state(self, i, s):
        """ sat (F_i and T and s')
        """
        self.solver.reset()
        
        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.pn_current.smtlib_transitions(0))
        self.solver.write(self.assert_equations())
        self.solver.write(s.smtlib(k=1, write_assert=True))
        
        return self.solver.check_sat()

    def sub_clause_finder_unsat_core(self, i, s):
        """ unsat core (-s and Fi and T and s')
        """
        self.solver.reset()

        self.solver.produce_unsat_core()
        
        self.solver.write(self.declare_places())
        self.solver.write(self.assert_formula(i))
        self.solver.write(self.pn_current.smtlib_transitions(0))
        self.solver.write(s.smtlib(0, write_assert=True, neg=True))
        self.solver.write(self.assert_equations())
        for eq in s.inequalities:
            self.solver.write("(assert (! {} :named {}))\n".format(eq.smtlib(1), eq.left_member.id))

        # Read Unsatisfiable Core
        unsat_core = self.solver.get_unsat_core()
        
        inequalities = []
        for eq in s.inequalities:
            if eq.left_member.id in unsat_core:
                if int(eq.right_member) == 0:
                    inequalities.append(Inequality(eq.left_member, eq.right_member, ">"))
                else:
                    inequalities.append(Inequality(eq.left_member, eq.right_member, "<"))
        cl = Clause(inequalities, "or")
        
        log.info("\t\t\t>> Clause learned: {}".format(cl))
        return cl

    def sub_clause_finder_mic(self, i, s):
        """ Miniman inductive clause (MIC)
        """
        c = copy.deepcopy(s)
        
        while len(c.inequalities) > 1:
            
            lit = c.inequalities.pop()
            
            self.solver.reset()
            self.solver.write(self.declare_places())
            self.solver.write(self.assert_formula(i))
            self.solver.write(self.pn_current.smtlib_transitions(0))
            self.solver.write(self.assert_equations())
            self.solver.write(c.smtlib(0, write_assert=True, neg=True))
            self.solver.write(c.smtlib(1, write_assert=True))

            if self.solver.check_sat():
                c.inequalities.append(lit)
                inequalities = []
                for eq in c.inequalities:
                    if int(eq.right_member) == 0:
                        inequalities.append(Inequality(eq.left_member, eq.right_member, "<"))
                cl = Clause(inequalities, "or")
                log.info("\t\t\t>> Clause learned: {}".format(cl))
                return cl

        inequalities = []
        for eq in s.inequalities:
                inequalities.append(Inequality(eq.left_member, eq.right_member, "<"))
        cl = Clause(inequalities, "or")
        log.info("\t\t\t>> Clause learned: {}".format(cl))
        return cl

    def cuber_filter(self, s):
        """ Extract a sub-cube with only non-null equalities,
            replace equalities by "greater or equal than".
        """
        non_zero = []
        for eq in s.inequalities:
            if eq.right_member != 0:
                non_zero.append(Inequality(eq.left_member, eq.right_member, ">="))
        return Clause(non_zero, "and")

    def prove(self):
        log.info("---IC3 RUNNING---\n")

        if self.init_marking_reach_bad_state() or self.init_tr_reach_bad_state():
            return False

        self.oars_initialization()

        k = 1

        while True:
            log.info("> F{} = P".format(k + 1))
            
            self.oars.append([self.P])
            if not self.strengthen(k):
                return False

            self.propagate_clauses(k)

            for i in range(1, k + 1):
                if set(self.oars[i]) == set(self.oars[i + 1]):
                    return True
            k += 1

    def strengthen(self, k):
        log.info("> Strengthen (k = {})".format(k))
        
        try:
            while self.formula_reach_bad_state(k):
                s = self.cuber_filter(self.solver.get_model(self.pn_current, 0))
                n = self.inductively_generalize(s, k - 2, k)
                
                log.info("\t\t>> s: {}".format(s))
                log.info("\t\t>> n: {}".format(n))
                
                self.push_generalization([(n + 1, s)], k)
            return True
        
        except Counterexample:
            return False

    def propagate_clauses(self, k):
        log.info("> Propagate Clauses (k = {})".format(k))
        
        for i in range(1, k + 1):
            for c in self.oars[i][1:]: # we do not look at the first clause that corresponds to I or P
                if not self.formula_reach_clause(i, c) and c not in self.oars[i + 1]:
                    self.oars[i + 1].append(c)

    def inductively_generalize(self, s, minimum, k):
            log.info("\t> Inductively Generalize (s = {} min = {}, k = {})".format(s, minimum, k))
     
            if minimum < 0 and self.state_reachable(0, s):
                raise Counterexample

            for i in range(max(1, minimum + 1), k + 1):
                
                if self.state_reachable(i, s):
                    self.generate_clause(s, i - 1, k)
                    return i - 1
            
            self.generate_clause(s, k, k)
            return k

    def generate_clause(self, s, i, k):
        log.info("\t\t\t> Generate Clause (i = {}, k = {})".format(i, k))
        
        c = self.sub_clause_finder(i, s)
        for j in range(1, i + 2):
            self.oars[j].append(c)

    def push_generalization(self, states, k):
        log.info("\t> Push generalization (k = {})".format(k))
        
        while True:
            state = min(states, key= lambda t: t[0])
            n, s = state[0], state[1]

            if n > k:
                return

            if self.formula_reach_state(n, s):
                p = self.cuber_filter(self.solver.get_model(self.pn_current, order=0))
                m = self.inductively_generalize(p, n - 2, k)
                states.append((m + 1, p))
            else:
                m = self.inductively_generalize(s, n, k)
                states.remove((n, s))
                states.append((m + 1, s))


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./ic3.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    log.basicConfig(format="%(message)s", level=log.DEBUG)

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, 'reachability')
    
    if len(sys.argv) == 2:
        pn_reduced = None
        eq = None
    else:
        pn_reduced = PetriNet(sys.argv[2])
        eq = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())

    ic3 = IC3(pn, formula, pn_reduced, eq)
    
    if ic3.prove():
        print("Proved")
    else:
        print("Counterexample")
