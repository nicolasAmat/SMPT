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
from subprocess import PIPE, Popen
from threading import Thread, Event

class IC3:
    """
    IC3 Method
    """
    def __init__(self, pn, formula):
        self.pn = pn
        self.formula = formula 
        self.oars = []
        self.solver = Popen(["z3", "-in"], stdin = PIPE, stdout = PIPE)

    def initialize(self):
        inequalities = []
        for pl, counter in self.pn.places.items():
            inequalities.append(Inequality(pl, counter, '='))
        self.oars.append(Clause(inequalities, 'and'))
        inequalities = []
        for ineq in self.formula.clauses:
            inequalities.append(Inequality(ineq.left_member, ineq.right_member, 'distinct'))
        self.oars.append(Clause(inequalities, 'or'))

    def declare_places(self, primes = True):
        if primes:
            return self.pn.smtlib_declare_places_ordered(0) \
                 + self.pn.smtlib_declare_places_ordered(1)
        else:
            return self.pn.smtlib_declare_places()

    def init_marking_check(self):
        smt_input = self.declare_places(False)   \
                  + self.pn.smtlib_set_marking() \
                  + self.formula.smtlib()
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def init_tr_check(self):
        smt_input = self.declare_places()                 \
                  + self.pn.smtlib_set_marking_ordered(0) \
                  + self.pn.smtlib_transitions_ordered(0) \
                  + self.formula.smtlib(1)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def inductive_invariant_check(self):
        smt_input = self.declare_places()                           \
                  + self.oars[1].smtlib(k = 0, write_assert = True) \
                  + self.pn.smtlib_transitions_ordered(0)           \
                  + self.formula.smtlib(1)
        print(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def solve(self):
        print("---IC3 running---\n")
        self.initialize()

        print("> INIT => P")
        self.init_marking_check()
        if self.formula.check_sat(self.solver):
            print("sat")
        else:
            print("unsat")
        self.solver.stdin.write(bytes("(reset)", 'utf-8'))
        
        print("> INIT and T => P")
        self.init_tr_check()
        if self.formula.check_sat(self.solver):
            print("sat")
        else:
            print("unsat")
        self.solver.stdin.write(bytes("(reset)", 'utf-8'))

        print("> P and T => P'")
        self.inductive_invariant_check()
        if self.formula.check_sat(self.solver):
            print("sat")
        else:
            print("unsat")
        self.solver.stdin.write(bytes("(reset)", 'utf-8'))

if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./ic3.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, 'reachability')
    
    ic3 = IC3(pn ,formula)
    ic3.solve()
