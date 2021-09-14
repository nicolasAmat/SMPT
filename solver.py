"""
Interface for z3 and MiniZinc solvers.

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

from subprocess import DEVNULL, PIPE, Popen
from tempfile import NamedTemporaryFile

import psutil

from formula import Atom, IntegerConstant, StateFormula, TokenCount
from utils import RESUME, STOP, SUSPEND, send_signal

# TODO v4: abstract class

class Solver:
    """
    Solver interface defined by:
    - a z3 process,
    - an 'aborted' flag,
    - a debug option.
    """

    def __init__(self, debug=False, timeout=0):
        """ Initializer.
        """
        process = ['z3', '-in']
        if timeout:
            process.append('-T:{}'.format(timeout))

        self.solver = Popen(process, stdin=PIPE, stdout=PIPE)
        self.aborted = False

        self.debug = debug

    def kill(self):
        """" Kill the process.
        """
        self.solver.kill()

    def suspend(self):
        """ Suspend the process.
        """
        send_signal([self.solver.pid], SUSPEND)

    def resume(self):
        """ Resume the process.
        """
        send_signal([self.solver.pid], RESUME)

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

        sat = self.readline()
        
        if sat == 'sat':
            return True
        elif sat == 'unsat':
            return False
        else:
            self.aborted = True
            return None

    # TODO v4: return a dictionnary to be consistent with `get_step` method
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


    # TODO v4: merge get_model and get_marking
    def get_marking(self, ptnet, order=None):
        """ Get a marking from the current SAT stack.
            Return a hashmap (keys: places and values: number of tokens).
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '(model '
        self.readline()

        # Parse the model
        model = {}
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
                model[ptnet.places[place]] = int(place_marking)

        return model

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
        self.file = NamedTemporaryFile('w', suffix='.mzn')
        self.solver = None
        self.aborted = False

        self.debug = debug
        self.timeout = timeout

        self.first_line = ""

    def kill(self):
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal([self.solver.pid], STOP)

        for proc in psutil.process_iter():
            if 'fzn-gecode' in proc.name():
                send_signal([proc.pid], STOP)

    def suspend(self):
        """ Suspend the process.
        """
        if self.solver is not None:
            send_signal([self.solver.pid], SUSPEND)

    def resume(self):
        """ Resume the process.
        """
        if self.solver is not None:
            send_signal([self.solver.pid], RESUME)

    def write(self, minizinc_input, debug=False):
        """ Write instructions into the standard input.
        """
        if self.debug or debug:
            print(minizinc_input)

        self.file.write(minizinc_input)
        self.file.flush()

    def readline(self, debug=False):
        """ Read a line from the standard output.
        """
        if self.solver is None:
            return ""

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

        process = ['minizinc', self.file.name]
        if self.timeout:
            process.extend(['--time-limit', str(self.timeout * 1000)])
        self.solver = Popen(process, stdout=PIPE, stderr=DEVNULL)

        minizinc_output = self.readline()
        self.first_line = minizinc_output

        if self.debug:
            print(minizinc_output)

        if minizinc_output in ["=====ERROR=====", "=====UNKNOWN====="]:
            self.aborted = True
            return None
        else:
            return minizinc_output != "=====UNSATISFIABLE====="

    def get_model(self, ptnet):
        """ Get a model.
            Return a cube (conjunction of equalities).
        """
        model = []
        line = self.first_line

        while line and line != '----------':
            place_content = line.split(' = ')

            if len(place_content) < 2:
                break

            self.parse_value(ptnet, place_content, model)

            line = self.readline()

        return StateFormula(model, 'and')

    def parse_value(self, ptnet, place_content, model):
        """ Parse a place from the model.
        """
        place_marking = int(place_content[1].replace(';', ''))
        place = place_content[0]

        if place_marking and place in ptnet.places:
            model.append(Atom(TokenCount([ptnet.places[place]]), IntegerConstant(int(place_marking)), '='))
