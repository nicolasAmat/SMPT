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

class IC3:
    """
    IC3 Method
    """
    def __init__(self, pn, formula):
        self.pn = pn
        self.formula = formula 
        self.oars = [] # list of CNF
        self.solver = Popen(["z3", "-in"], stdin = PIPE, stdout = PIPE)

    def declare_places(self, primes = True):
        if primes:
            return self.pn.smtlib_declare_places_ordered(0) \
                 + self.pn.smtlib_declare_places_ordered(1)
        else:
            return self.pn.smtlib_declare_places()
    
    def oars_initialization(self):
        print("> F0 = I and Fi = P")
        inequalities = []
        for pl in self.pn.places.values():
            inequalities.append(Inequality(pl, pl.marking, '='))
        self.oars.append([Clause(inequalities, 'and')])
        inequalities = []
        for ineq in self.formula.clauses:
            inequalities.append(Inequality(ineq.left_member, ineq.right_member, 'distinct'))
        self.oars.append([Clause(inequalities, 'or')])

    def init_marking_sat(self):
        print("> INIT => P")
        self.solver.stdin.write(bytes("(reset)\n", 'utf-8'))
        self.solver.stdin.flush()
        smt_input = self.declare_places(False)   \
                  + self.pn.smtlib_set_marking() \
                  + self.formula.smtlib()
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)
            

    def init_tr_sat(self):
        print("> INIT and T => P")
        self.solver.stdin.write(bytes("(reset)\n", 'utf-8'))
        self.solver.stdin.flush()
        smt_input = self.declare_places()                 \
                  + self.pn.smtlib_set_marking_ordered(0) \
                  + self.pn.smtlib_transitions_ordered(0) \
                  + self.formula.smtlib(1)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)
           
        
    def inductive_invariant_check(self):
        self.solver.stdin.write(bytes("(reset)\n", 'utf-8'))
        self.solver.stdin.flush()
        smt_input = self.declare_places()
        for clause in self.oars[len(self.oars) - 1]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        smt_input += self.pn.smtlib_transitions_ordered(0) \
                   + self.formula.smtlib(1)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def state_reachable(self, cube):
        self.solver.stdin.write(bytes("(reset)\n", 'utf-8'))
        self.solver.stdin.flush()
        smt_input = self.declare_places()
        for clause in self.oars[len(self.oars) - 2]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        smt_input += self.pn.smtlib_transitions_ordered(0) \
                   + cube.smtlib(k=1, write_assert=True)
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        return self.formula.check_sat(self.solver)

    def sub_cube_finder(self, cube):
        self.solver.stdin.write(bytes("(reset)\n", 'utf-8'))
        self.solver.stdin.flush()
        smt_input = "(set-option :produce-unsat-cores true)\n" \
                  + self.declare_places()                      \
                  + self.pn.smtlib_transitions_ordered(0)
        for clause in self.oars[len(self.oars) - 2]:
            smt_input += clause.smtlib(k=0, write_assert=True)
        for eq in cube.inequalities:
            smt_input += "(assert (! {} :named {}))\n".format(eq.smtlib(k=1), eq.left_member.id)
        smt_input += "(check-sat)\n(get-unsat-core)\n"
        self.solver.stdin.write(bytes(smt_input, 'utf-8'))
        self.solver.stdin.flush()

        # Read "unsat"
        self.solver.stdout.readline().decode('utf-8').strip()
        # Read Unsatisfiable Core
        sub_cube = self.solver.stdout.readline().decode('utf-8').strip().replace('(', '').replace(')', '').split(' ') 
        for eq in cube.inequalities:
            if eq.left_member.id not in sub_cube:
                cube.remove(eq)

    # METHODE EN DEBUG
    def prove(self):
        print("---IC3 running---\n")

        if self.init_marking_sat() or self.init_tr_sat():
            return False 

        self.oars_initialization()
        
        # # Check that P is an inductive invariant
        # print("> P and T => P'")
        # if self.inductive_invariant_check():
        #     print("P is an inductive invariant! We won the war...")
        #     exit(0)
        
        # # while self.formula.check_sat(self.solver):
        # cube = self.formula.get_model(self.solver, 0)
        # if self.state_reachable(cube):
        #     print("CEX")
        #     exit(0)
        # else:
        #     self.sub_cube_finder(cube)

        # self.solver.stdin.write(bytes("(reset)", 'utf-8'))




if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./ic3.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    formula = Formula(pn, 'reachability')
    
    ic3 = IC3(pn ,formula)
    ic3.prove()
