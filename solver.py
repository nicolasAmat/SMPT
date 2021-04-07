#!/usr/bin/env python3

"""
z3 Interface

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
__version__ = "3.0.0"

from subprocess import PIPE, Popen

from properties import Atom, IntegerConstant, StateFormula, TokenCount


class Solver:
    """
    Solver interface defined by:
    - a z3 process,
    - a debug option.
    """

    def __init__(self, debug=False, timeout=0):
        """ Initializer.
        """
        process = ['z3', '-in']
        if timeout:
            process.append('-T:{}'.format(timeout))
        self.solver = Popen(process, stdin=PIPE, stdout=PIPE)
        self.debug = debug

    def kill(self):
        """" Kill the process.
        """
        self.solver.kill()

    def write(self, smt_input, debug=False):
        """ Write instructions into the standard input.
        """
        if self.debug or debug:
            print(smt_input)

        if smt_input != "":
            try:
                self.solver.stdin.write(bytes(smt_input, 'utf-8'))
            except BrokenPipeError:
                return ""

    def flush(self):
        """ Flush the standard input.
        """
        try:
            self.solver.stdin.flush()
        except BrokenPipeError:
            return

    def readline(self, debug=False):
        """ Read a line from the standard output.
        """
        try:
            smt_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            return ""

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
            Creates a new scope by saving the current stack size.
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

    # TODO: return a dictionnary to be consistent with `get_step` method
    def get_model(self, ptnet, order=None):
        """ Get a model from the current SAT stack.
            Return a cube (conjunction of equalities).
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '(model '
        self.readline()

        # Parse the model
        model = []
        while True:
            place_content = self.readline().split(' ')
            
            # Check if parsing done
            if len(place_content) < 2:
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

    def get_step(self, ptnet):
        """ Get a step from the current SAT stack,
            meaning a pair of markings (m, m') s.t. m -> m'
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '(model '
        self.readline()

        # Parse the model
        markings = [{}, {}]
        while True:
            place_content = self.readline().split(' ')

            # Check if parsing done
            if len(place_content) < 2:
                break

            # Get place marking and place id
            place_marking = int(self.readline().replace(' ', '').replace(')', ''))
            place_content = place_content[1].split('@')
            place_id = place_content[0]

            # Add the place marking in the corresponding dictionnary
            markings[int(place_content[1])][ptnet.places[place_id]] = place_marking

        return markings[0], markings[1]

    def enable_unsat_core(self):
        """ Enable generation of unsat cores.
        """
        self.write("(set-option :produce-unsat-cores true)\n")

    def get_unsat_core(self):
        """ Get an unsat core from the current UNSAT stack.
        """
        assert (not self.check_sat())

        self.write("(get-unsat-core)\n")
        self.flush()

        return self.readline().replace('(', '').replace(')', '').split(' ')


class MiniZinc:
    """ Specific MiniZinc interface defined by:
        - a MiniZinc process,
        - a debug option.
    """

    def __init__(self, debug=False, timeout=0):
        """ Initializer.
        """
        process = ['minizinc', '-']
        if timeout:
            process.extend(['--time-limit', str(timeout * 1000)])
        self.solver = Popen(process, stdin=PIPE, stdout=PIPE, stderr=PIPE)
        self.debug = debug

        self.first_value = ""

    def kill(self):
        """" Kill the process.
        """
        self.solver.kill()

    def write(self, minizinc_input, debug=False):
        """ Write instructions into the standard input.
        """
        if self.debug or debug:
            print(minizinc_input)

        if minizinc_input != "":
            try:
                self.solver.stdin.write(bytes(minizinc_input, 'utf-8'))
            except BrokenPipeError:
                return ""

    def readline(self, debug=False):
        """ Read a line from the standard output.
        """
        try:
            minizinc_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            return ""

        if self.debug or debug:
            print(minizinc_output)

        return minizinc_output

    def set_bound(self):
        """ Set integer bound.
        """
        self.write("int: MAX = 1000000;\n")

    def check_sat(self):
        """ Check the satisfiability.
        """
        self.write("solve satisfy;\n")
        try:
            self.solver.stdin.close()
        except BrokenPipeError:
            return False
        
        minizinc_output = self.readline()

        if ';' in minizinc_output:
            self.first_value = minizinc_output

        return minizinc_output != "=====UNSATISFIABLE====="

    def get_model(self, ptnet):
        """ Get a model.
            Return a cube (conjunction of equalities).
        """
        model = []

        place_content = self.first_value.split(' = ')
        self.parse_value(ptnet, place_content, model)

        while True:
            place_content = self.readline().split(' = ')

            if len(place_content) < 2:
                break

            self.parse_value(ptnet, place_content, model)

        return StateFormula(model, 'and')

    def parse_value(self, ptnet, place_content, model):
        """ Parse a place from the model.
        """
        place_marking = int(place_content[1].replace(';', ''))
        place = place_content[0]

        if place_marking and place in ptnet.places:
            model.append(Atom(TokenCount([ptnet.places[place]]), IntegerConstant(int(place_marking)), '='))
