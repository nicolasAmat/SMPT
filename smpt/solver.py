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
__version__ = "4.0.0"

import logging as log
import os
import sys
from abc import ABC, abstractmethod
from subprocess import DEVNULL, PIPE, Popen
from tempfile import NamedTemporaryFile

from ptnet import Marking
from utils import KILL, STOP, send_signal_pids


class Solver(ABC):
    """ Solver abstract class.
        (Z3, MiniZinc, Walk)
    """

    @abstractmethod
    def kill(self):
        """" Kill the process.
        """
        pass

    @abstractmethod
    def write(self, input):
        """ Write instructions.
        """
        pass

    @abstractmethod
    def check_sat(self):
        """
        """
        pass

    @abstractmethod
    def get_marking(self):
        """
        """
        pass


class Z3(Solver):
    """
    z3 interface defined by:
    - a z3 process,
    - an 'aborted' flag,
    - a debug option.
    """

    def __init__(self, debug=False, timeout=0, solver_pids=None):
        """ Initializer.
        """
        # Solver
        process = ['z3', '-in']
        if timeout:
            process.append('-T:{}'.format(timeout))
        self.solver = Popen(process, stdin=PIPE, stdout=PIPE, start_new_session=True)

        if solver_pids is not None:
            solver_pids.put(self.solver.pid)

        # Flags
        self.aborted = False
        self.debug = debug

    def kill(self):
        """" Kill the process.
        """
        self.solver.kill()

    def abort(self):
        """ Abort the process.
        """
        log.warning("z3 process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

    def write(self, smt_input, debug=False):
        """ Write instructions into the standard input.
        """
        if self.debug or debug:
            print(smt_input)

        if smt_input != "":
            try:
                self.solver.stdin.write(bytes(smt_input, 'utf-8'))
            except BrokenPipeError:
                self.abort()

    def flush(self):
        """ Flush the standard input.
        """
        try:
            self.solver.stdin.flush()
        except BrokenPipeError:
            self.abort()

    def readline(self, debug=False):
        """ Read a line from the standard output.
        """
        try:
            smt_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

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

    def check_sat(self, no_check=False):
        """ Check the satisfiability of the current stack of z3.
        """
        self.write("(check-sat)\n")
        self.flush()

        sat = self.readline()

        if sat == 'sat':
            return True
        elif sat == 'unsat':
            return False
        elif no_check:
            return None
        else:
            self.abort()

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
        marking = {}
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
                place_content = place_content[1].rsplit('@', 1)
                if int(place_content[1]) == order:
                    place = place_content[0]
            if place_marking and place in ptnet.places:
                marking[ptnet.places[place]] = int(place_marking)

        return Marking(marking)

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
            place_content = place_content[1].rsplit('@', 1)
            place_id = place_content[0]
            # Skip free variables
            if place_id not in ptnet.places:
                continue

            # Add the place marking in the corresponding dictionnary
            markings[int(place_content[1])][ptnet.places[place_id]] = place_marking

        return Marking(markings[0]), Marking(markings[1])

    def get_trap(self, ptnet):
        """ Get trap from the current SAT stack.
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '(model '
        self.readline()

        # Parse the model
        trap = set()
        while True:
            content = self.readline().split(' ')
            
            # Check if parsing done
            if len(content) < 2:
                break

            is_trap = self.readline().replace(' ', '').replace(')', '') == "true"
            place = content[1]

            if is_trap and place in ptnet.places:
                trap.add(ptnet.places[place])

        return trap

    def enable_unsat_core(self):
        """ Enable generation of unsat cores.
        """
        self.write("(set-option :produce-unsat-cores true)\n")

    def get_unsat_core(self):
        """ Get an unsat core from the current UNSAT stack.
        """
        sat = self.check_sat(no_check=True)
        
        # Assert the result either `UNKNOWN` or `SAT`
        assert(sat is None or not sat)

        # If `UNKNOWN` consider that the solver is still alive and return "All" as the unsat core
        if sat is None:
            return ["All"]

        self.write("(get-unsat-core)\n")
        self.flush()

        return self.readline().replace('(', '').replace(')', '').split(' ')


class MiniZinc(Solver):
    """ Specific MiniZinc interface defined by:
        - a MiniZinc process,
        - a debug option.
    """

    def __init__(self, debug=False, timeout=0, solver_pids=None):
        """ Initializer.
        """
        # File to write formula
        self.file = NamedTemporaryFile('w', suffix='.mzn')
        
        # Solver
        self.solver = None
        self.solver_pids = solver_pids

        # Flags
        self.aborted = False
        self.debug = debug
        self.timeout = timeout

        self.first_line = ""

    def kill(self):
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal_pids([self.solver.pid], STOP)

    def abort(self):
        """ Abort the process.
        """
        log.warning("MiniZinc process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

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
            self.abort()

        try:
            minizinc_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

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
        self.solver = Popen(process, stdout=PIPE, stderr=DEVNULL, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        minizinc_output = self.readline()
        self.first_line = minizinc_output

        if self.debug:
            print(minizinc_output)

        if minizinc_output in ["=====ERROR=====", "=====UNKNOWN====="]:
            self.abort()
        else:
            return minizinc_output != "=====UNSATISFIABLE====="

    def get_marking(self, ptnet):
        """ Get a model.
            Return a cube (conjunction of equalities).
        """
        marking = {}
        line = self.first_line

        while line and line != '----------':
            place_content = line.split(' = ')

            if len(place_content) < 2:
                break

            self.parse_value(ptnet, place_content, marking)

            line = self.readline()

        return Marking(marking)

    def parse_value(self, ptnet, place_content, marking):
        """ Parse a place from the model.
        """
        place_marking = int(place_content[1].replace(';', ''))
        place = place_content[0]

        if place_marking and place in ptnet.places:
            marking[ptnet.places[place]] = place_marking


class Walk(Solver):
    """ Walk interface.
    """
    
    def __init__(self, ptnet, debug=False, timeout=0, solver_pids=None):
        """ Initializer.
        """
        # Petri net
        self.ptnet = ptnet

        # Solver
        self.solver = None
        self.timeout = timeout
        self.solver_pids = solver_pids

        # Flags
        self.debug = debug
        self.aborted = False

    def kill(self):
        """" Kill the process.
        """
        if self.solver is not None:
            send_signal_pids([self.solver.pid], KILL)

    def abort(self):
        """ Abort the process.
        """
        log.warning("Walk process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

    def readline(self, debug=False):
        """ Readline from walk.
        """
        try:
            output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(output)

        return output

    def check_sat(self, walk_filename):
        """ Check if a state violates the formula.
        """
        process = ['walk', '-R', '-loop', '-seed', self.ptnet.filename, '-ff', walk_filename]
        if self.timeout:
            process += ['-t', str(self.timeout)]
        self.solver = Popen(process, stdout=PIPE, start_new_session=True)

        if self.solver_pids is not None:
            self.solver_pids.put(self.solver.pid)

        return not (self.readline() != 'FALSE')

    def write(self, input):
        """ Write input to file.
        """
        raise NotImplementedError

    def get_marking(self):
        """
        """
        raise NotImplementedError

