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
from formula import Formula

import sys
from subprocess import PIPE, Popen
from threading import Thread, Event

class IC3:
    """
    IC3 method
    """
    def __init__(self, pn, formula):
        self.pn = pn
        self.formula = formula 
        self.oars = []
        self.solver = Popen(["z3", "-in"], stdin = PIPE, stdout = PIPE)

    def declare_places(self, primes = True):
        smt_input = ""
        smt_input += self.pn.smtlib_declare_places()
        if primes:
            smt_input += self.pn.smtlib_declare_places_ordered(1)
        print(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def init_marking_check(self):
        smt_input = ""
        smt_input += self.pn.smtlib_set_marking()
        smt_input += self.formula.smtlib()
        print(smt_input)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def solve(self):
        print("---IC3 running---")
        self.declare_places(False)
        self.init_marking_check()

if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./ic3.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, 'reachability')
    
    ic3 = IC3(pn ,formula)
    ic3.solve()
