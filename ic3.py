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

    def declare_places(self, primes = True):
        smt_input = ""
        if primes:
            smt_input += self.pn.smtlib_declare_places_ordered(0)
            smt_input += self.pn.smtlib_declare_places_ordered(1)
        else:
            smt_input += self.pn.smtlib_declare_places()
        print(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def init_marking_check(self):
        self.declare_places(False)
        smt_input = ""
        smt_input += self.pn.smtlib_set_marking()
        smt_input += self.formula.smtlib()
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def init_tr_check(self):
        self.declare_places()
        smt_input = ""
        smt_input += self.pn.smtlib_set_marking_ordered(0)
        smt_input += self.pn.smtlib_transitions_ordered(0)
        smt_input += self.formula.smtlib(1)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def inductive_invariant_check(self):
        self.declare_places()
        smt_input = ""
        
        smt_input += self.pn.smtlib_transitions_ordered(0)
        smt_input += self.formula.smtlib(1)

    def solve(self):
        print("---IC3 running---\n")
        
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
        

if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./ic3.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, 'reachability')
    
    ic3 = IC3(pn ,formula)
    ic3.solve()
