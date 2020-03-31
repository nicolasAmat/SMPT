#!/usr/bin/env python3

"""
Z3 interface

Using SMT-LIB v2 format
Standard: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf

Dependency: https://github.com/Z3Prover/z3

This module can easily be hacked to replace Z3
by an other SMT solver supporting the SMT-LIB format.
"""

from subprocess import PIPE, Popen

class Solver:
    """
    Solver defined:
    - a Z3 solver process
    """
    def __init__(self):
        self.solver = Popen(["z3", "-in"], stdin = PIPE, stdout = PIPE)

    def write(self, text):
        self.solver.stdin.write(bytes(text, 'utf-8'))
        self.solver.stdin.flush()

    def reset(self):
        self.write("(reset)\n")

    def exit(self):
        self.write("(exit)\n")

    def check_sat(self):
        self.write("(check-sat)\n")
        return self.solver.stdout.readline().decode('utf-8').strip() == 'sat'

    def get_model(self, pn, order = None):
        self.write("(get-model)\n")

        model = []

        # Read the model
        self.solver.stdout.readline()

        # Parse the model
        while True:
            place_content = self.solver.stdout.readline().decode('utf-8').strip().split(' ')
           
            if len(place_content) < 2 or self.solver.poll() is not None:
                break

            place_marking =  self.solver.stdout.readline().decode('utf-8').strip().replace(' ', '').replace(')', '')
            
            place = ""
            if order is None:
                place = place_content[1]
            else:
                place_content = place_content[1].split('@')
                if int(place_content[1]) == order:
                    place = place_content[0]

        #TODO: continue
        return model


if __name__ == '__main__':
    pass