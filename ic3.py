#!/usr/bin/env python3

"""
IC3:
Incremental Construction of
Inductive Clauses for Indubitable Correctness

Based on "SAT-Based Model Checking without Unrolling"
Aaron Bradley, VMCAI 2011
"""

from pn import PetriNet
from eq import System
from formula import Formula, Clause, Inequality

import sys
import copy
from subprocess import PIPE, Popen
from threading import Thread, Event


class Counterexample(Exception):
    pass


class IC3:
    """
    IC3 Method
    """
    def __init__(self, pn, formula):
        self.pn = pn
        self.formula = formula 
        self.P = None
        self.oars = [] # list of CNF
        self.solver = Popen(["z3", "-in"], stdin = PIPE, stdout = PIPE)
        self.f = open("debug2.smt2", "w")

    def declare_places(self, primes = True):
        if primes:
            return self.pn.smtlib_declare_places_ordered(0) \
                 + self.pn.smtlib_declare_places_ordered(1)
        else:
            return self.pn.smtlib_declare_places()
    
    def oars_initialization(self):
        print("> F0 = I and F1 = P")
        inequalities = []
        for pl in self.pn.places.values():
            inequalities.append(Inequality(pl, pl.marking, '='))
        self.oars.append([Clause(inequalities, 'and')])
        inequalities = []
        for ineq in self.formula.clauses:
            inequalities.append(Inequality(ineq.left_member, ineq.right_member, 'distinct'))
        self.P = Clause(inequalities, 'or')
        self.oars.append([self.P])

    def init_marking_sat(self):
        print("> INIT => P")
        smt_input = "(reset)\n"                  \
                  + self.declare_places(False)   \
                  + self.pn.smtlib_set_marking() \
                  + self.formula.smtlib()
        #self.f.write(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def init_tr_sat(self):
        print("> INIT and T => P")
        smt_input = "(reset)\n"                           \
                  + self.declare_places()                 \
                  + self.pn.smtlib_set_marking_ordered(0) \
                  + self.pn.smtlib_transitions_ordered(0) \
                  + self.formula.smtlib(1)
        #self.f.write(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def inductive_invariant_sat(self, k):
        smt_input = "(reset)\n"           \
                  + self.declare_places()
        for clause in self.oars[k]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        smt_input += self.pn.smtlib_transitions_ordered(0) \
                   + self.formula.smtlib(1)
        # self.f.write(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def formula_reach_clause_sat(self, index_formula, c):
        smt_input = "(reset)\n"           \
                  + self.declare_places()
        for clause in self.oars[index_formula]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        smt_input += self.pn.smtlib_transitions_ordered(0) \
                   + c.smtlib(k=1, write_assert=True, neg=True)
        #self.f.write(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def strengthen(self, k):
        try:
            while self.inductive_invariant_sat(k):
                s = self.formula.get_model(self.solver, 0)
                n = self.inductively_generalize(s, k - 2, k)
                self.push_generalization([(n + 1, s)], k)
            return True
        except Counterexample: #Counterexample
            return False

    def state_reachable(self, index_formula, s):
        smt_input = "(reset)\n"                                \
                  + self.declare_places()                      \
                  + s.smtlib(k=0, write_assert=True, neg=True)
        for clause in self.oars[index_formula]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        smt_input += self.pn.smtlib_transitions_ordered(0) \
                   + s.smtlib(k=1, write_assert=True)
        #self.f.write(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def inductively_generalize(self, s, minimum, k):
        if minimum < 0 and self.state_reachable(0, s):
            raise Counterexample

        for i in range(max(1, minimum + 1), k):
            if self.state_reachable(i, s):
                self.generate_clause(s, i - 1, k)
                return i - 1
        print(k)
        self.generate_clause(s, k, k)
        return k
        
    def propagate_clauses(self, k):
        for i in range(k):
            for c in self.oars[i][1:]: # we do not look at the first clause that corresponds to I or P
                if not self.formula_reach_clause_sat(i, c):
                    self.oars[i + 1].append(c)

    def generate_clause(self, s, i, k):
        c = self.sub_cube_finder_from_clause(i, s)
        for j in range(1, i+1):
            self.oars[j].append(c)

    def sub_cube_finder_from_clause(self, i, cube):
        smt_input = "(reset)\n(set-option :produce-unsat-cores true)\n" \
                  + self.declare_places()                               \
                  + self.pn.smtlib_transitions_ordered(0)
        for clause in self.oars[i]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        for eq in cube.inequalities:
            smt_input += "(assert (! {} :named {}))\n".format(eq.smtlib(k=1), eq.left_member.id)
        smt_input += "(check-sat)\n(get-unsat-core)\n"
        #self.f.write(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        self.solver.stdin.flush()

        # Read "unsat"
        self.solver.stdout.readline().decode('utf-8').strip()
        # Read Unsatisfiable Core
        sub_cube = self.solver.stdout.readline().decode('utf-8').strip().replace('(', '').replace(')', '').split(' ') 
        
        # Generate the clause corresponding to $\neg c$
        inequalities = []
        for eq in cube.inequalities:
            if eq.left_member.id in sub_cube:
                inequalities.append(Inequality(eq.left_member, eq.right_member, "distinct"))
        return Clause(inequalities, "or")

    def formula_reach_sat(self, index_formula, s):
        smt_input = "(reset)\n"           \
                  + self.declare_places()
        for clause in self.oars[index_formula]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        smt_input += self.pn.smtlib_transitions_ordered(0) \
                   + s.smtlib(k=1, write_assert=True)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def push_generalization(self, states, k):
        while True:
            state = min(states, key= lambda t: t[0])
            n, s = state[0], state[1]

            if n > k:
                return

            if self.formula_reach_sat(n, s):
                p = self.formula.get_model(self.solver, order=0)
                m = self.inductively_generalize(p, n - 2, k)
                states.append((m + 1, p))
            else:
                m = self.inductively_generalize(s, n, k)
                states.remove((n, s)).append((m + 1, s))


    def prove(self):
        print("---IC3 running---\n")

        if self.init_marking_sat() or self.init_tr_sat():
            return False 

        self.oars_initialization()
        
        k = 1

        while True:
            self.oars.append([self.P])

            if not self.strengthen(k):
                print("Not proved")
                return False
            
            self.propagate_clauses(k)

            for i in range(1, k):
                if set(self.oars[i]) == set(self.oars[i + 1]):
                    print("Proved")
                    return True

            k += 1



if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./ic3.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, 'reachability')
    
    ic3 = IC3(pn ,formula)
    ic3.prove()
