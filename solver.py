#!/usr/bin/env python3

"""
Z3 interface

Uses SMT-LIB v2 format
Standard: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf

Dependency: https://github.com/Z3Prover/z3

This module can easily be hacked to replace Z3
by another SMT solver supporting the SMT-LIB format.

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
__version__ = "2.0.0"

from subprocess import PIPE, Popen

from properties import Atom, IntegerConstant, StateFormula, TokenCount


class Solver:
    """
    Solver interface defined by:
    - a z3 process,
    - a debug option.
    """

    def __init__(self, debug=False):
        """ Initializer.
        """
        self.solver = Popen(["z3", "-in"], stdin=PIPE, stdout=PIPE)
        self.debug = debug

    def exit(self):
        """" Exit.
        """
        self.write("(exit)\n")
        self.solver.stdin.close()
        self.solver.stdout.close()

    def write(self, smt_input, debug=False):
        """ Write instructions into the standard input.
        """
        if self.debug or debug:
            print(smt_input)
        
        if smt_input != "":
            self.solver.stdin.write(bytes(smt_input, 'utf-8'))

    def flush(self):
        """ Flush the standard input.
        """
        self.solver.stdin.flush()

    def readline(self, debug=False):
        """ Read a line from the standard output.
        """
        smt_output = self.solver.stdout.readline().decode('utf-8').strip()
        
        if self.debug or debug:
            print(smt_output)
        
        return smt_output

    def reset(self):
        """ Reset.
            Erase all assertions and declarations.
        """
        self.write("(reset)\n")

    def push(self):
        """ Push.
            Creates a new scope by saving the current stack size
        """
        self.write("(push)\n")

    def pop(self):
        """ Pop.
            Removes any assertion or declaration performed between it and the matching push.
        """
        self.write("(pop)\n")

    def check_sat(self):
        """ Check the satisfiability of the current stack of z3.
        """
        self.write("(check-sat)\n")
        self.flush()

        return self.readline() == 'sat'

    def get_model(self, ptnet, order=None):
        """ Get a model from the current SAT stack.
            Return a cube (conjunction of equalities).
        """
        self.write("(get-model)\n")
        self.flush()
        
        # Read '(model '
        self.readline()

        # Parse the model
        model = []
        while True:
            place_content = self.readline().split(' ')
            
            if len(place_content) < 2 or self.solver.poll() is not None:
                break
            
            place_marking = self.readline().replace(' ', '').replace(')', '')
            place = ""
            if order is None:
                place = place_content[1]
            else:
                place_content = place_content[1].split('@')
                if int(place_content[1]) == order:
                    place = place_content[0]
            if place_marking and place in ptnet.places:
                model.append(Atom(TokenCount([ptnet.places[place]]), IntegerConstant(int(place_marking)), '='))

        return StateFormula(model, 'and')

    def enable_unsat_core(self):
        """ Enable generation of unsat cores.
        """
        self.write("(set-option :produce-unsat-cores true)\n")

    def get_unsat_core(self):
        """ Get an unsat core.
            From the current UNSAT stack.
            Return a clause (disjunctive).
        """
        assert (not self.check_sat())
        
        self.write("(get-unsat-core)\n")
        self.flush()

        return self.readline().replace('(', '').replace(')', '').split(' ')

    def display_model(self, ptnet, order=None):
        """ Display the resulting model.
        """
        model = ""
        
        for place_marking in self.get_model(ptnet, order).operands:
            if place_marking.right_operand.value > 0:
                model += " {}({})".format(place_marking.left_operand, place_marking.right_operand)
        
        if model == "":
            model = " empty marking"
        
        print("Model:", model, sep='')
