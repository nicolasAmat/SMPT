
"""
z3 Interface

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

from __future__ import annotations

__author__ = "Nicolas AMAT, LAAS-CNRS"
__contact__ = "namat@laas.fr"
__license__ = "GPLv3"
__version__ = "4.0.0"

import logging as log
import sys
from multiprocessing import Queue
from subprocess import PIPE, Popen
from typing import Optional

from smpt.interfaces.solver import Solver
from smpt.ptio.ptnet import Marking, PetriNet, Place, Transition


class Z3(Solver):
    """ z3 interface.

    Note
    ----
    Uses SMT-LIB v2 format
    Standard: http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf

    Dependency: https://github.com/Z3Prover/z3

    This class can easily be hacked to replace Z3
    by another SMT solver supporting the SMT-LIB format.

    Attributes
    ----------
    solver : Popen
        A z3 process.
    aborted : bool
        Aborted flag.
    debug : bool
        Debugging flag.
    """

    def __init__(self, debug: bool = False, timeout: int = 0, solver_pids: Queue = None) -> None:
        """ Initializer.

        Parameters
        ----------
        debug : bool, optional
            Debugging flag.
        timeout : int, optional
            Timeout of the solver.
        solver_pids : Queue of int, optional
            Queue of solver pids.
        """
        # Solver
        process = ['z3', '-in']
        if timeout:
            process.append('-T:{}'.format(timeout))
        self.solver: Popen = Popen(process, stdin=PIPE,
                                   stdout=PIPE, start_new_session=True)

        if solver_pids is not None:
            solver_pids.put(self.solver.pid)

        # Flags
        self.aborted: bool = False
        self.debug: bool = debug

    def kill(self) -> None:
        """" Kill the process.
        """
        self.solver.kill()

    def abort(self) -> None:
        """ Abort the solver.
        """
        log.warning("z3 process has been aborted")
        self.solver.kill()
        self.aborted = True
        sys.exit()

    def write(self, input: str, debug: bool = False) -> None:
        """ Write instructions to the standard input.

        Parameters
        ----------
        input : str 
            Input instructions.
        debug : bool
            Debugging flag.
        """
        if self.debug or debug:
            print(input)

        if input != "":
            try:
                self.solver.stdin.write(bytes(input, 'utf-8'))
            except BrokenPipeError:
                self.abort()

    def flush(self) -> None:
        """ Flush the standard input.
        """
        try:
            self.solver.stdin.flush()
        except BrokenPipeError:
            self.abort()

    def readline(self, debug: bool = False):
        """ Read a line from the standard output.

        Parameters
        ----------
        debug : bool, optional
            Debugging flag.

        Returns
        -------
        str
            Line read.
        """
        try:
            smt_output = self.solver.stdout.readline().decode('utf-8').strip()
        except BrokenPipeError:
            self.abort()

        if self.debug or debug:
            print(smt_output)

        return smt_output

    def reset(self) -> None:
        """ Reset.

        Note
        ----
        Erase all assertions and declarations.
        """
        self.write("(reset)\n")

    def push(self):
        """ Push.

        Note
        ----
        Creates a new scope by saving the current stack size.
        """
        self.write("(push)\n")

    def pop(self) -> None:
        """ Pop.

        Note
        ----
        Removes any assertion or declaration performed between it and the last push.
        """
        self.write("(pop)\n")

    def check_sat(self, no_check: bool = False) -> Optional[bool]:
        """ Check the satisfiability of the current stack of z3.

        Parameters
        ----------
        no_check : bool
            Do not abort the solver in case of unknown verdict.

        Returns
        -------
        bool, optional
            Satisfiability of the current stack.
        """
        self.write("(check-sat)\n")
        self.flush()

        sat = self.readline()

        if sat == 'sat':
            return True
        elif sat == 'unsat':
            return False
        elif not no_check:
            self.abort()

        return None

    def get_marking(self, ptnet: PetriNet, order: Optional[int] = None) -> Marking:
        """ Get a marking from the current SAT stack.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.
        order : int, optional
            Order.

        Returns
        -------
        Marking : 
            Marking from the current SAT stack.
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '( '
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

    def get_parikh(self, ptnet: PetriNet) -> set[Transition]:
        """ Get a parikh set (non a vector) from the current SAT stack.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.

        Returns
        -------
        set of Transition : 
            Set of transitions from the parikh vector
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '( '
        self.readline()

        # Parse the model
        parikh = set()
        while True:
            transition_content = self.readline().split(' ')

            # Check if parsing done
            if len(transition_content) < 2:
                break

            occurences = self.readline().replace(' ', '').replace(')', '')
            transition = ""
            transition_content = transition_content[1].rsplit('@', 1)
            if len(transition_content) > 1 and transition_content[1] == "t":
                transition = transition_content[0]
                if int(occurences) > 0:
                    parikh.add(ptnet.transitions[transition])

        return parikh

    def get_trace(self, ptnet: PetriNet, length: int) -> list[str]:
        """ Get the trace from the current SAT stack.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.
        length : int
            Length of the trace.

        Returns
        -------
        list of str
            Trace (ordered list of transition ids)
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '(model '
        self.readline()

        # Parse the model
        trace = ["" for _ in range(length)]

        while True:
            content = self.readline().split(' ')

            # Check if parsing done
            if len(content) < 2:
                break

            id = self.readline().replace(' ', '').replace(')', '')

            # Get place marking and place id
            content = content[1].rsplit('@', 1)

            if content[0] == "TRACE" and id != "(-1":
                trace[int(content[1])] = list(
                    ptnet.transitions.keys())[int(id)]

        return trace

    def get_step(self, ptnet: PetriNet) -> tuple[Marking, Marking]:
        """ Get a step from the current SAT stack,
            meaning a pair of markings (m, m') s.t. m -> m'

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.
        
        Returns
        -------
        tuple of Marking, Marking
            m and m' from the current stack.
        """
        # Solver instruction
        self.write("(get-model)\n")
        self.flush()

        # Read '(model '
        self.readline()

        # Parse the model
        markings: list[dict[Place, int]] = [{}, {}]
        while True:
            place_content = self.readline().split(' ')

            # Check if parsing done
            if len(place_content) < 2:
                break

            # Get place marking and place id
            place_marking = int(
                self.readline().replace(' ', '').replace(')', ''))
            place_content = place_content[1].rsplit('@', 1)
            place_id = place_content[0]
            # Skip free variables
            if place_id not in ptnet.places:
                continue

            # Add the place marking in the corresponding dictionnary
            markings[int(place_content[1])
                     ][ptnet.places[place_id]] = place_marking

        return Marking(markings[0]), Marking(markings[1])

    def get_trap(self, ptnet: PetriNet) -> set[Place]:
        """ Get trap from the current SAT stack.

        Parameters
        ----------
        ptnet : PetriNet
            Current Petri net.

        Returns
        -------
        set of Place
            Trap from the current stack.
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

    def enable_unsat_core(self) -> None:
        """ Enable generation of unsat cores.
        """
        self.write("(set-option :produce-unsat-cores true)\n")

    def get_unsat_core(self) -> str:
        """ Get an unsat core from the current UNSAT stack.

        Returns
        -------
        str
            Unsat core.
        """
        sat = self.check_sat(no_check=True)

        # Assert the result either `UNKNOWN` or `SAT`
        assert (sat is None or not sat)

        # If `UNKNOWN` consider that the solver is still alive and return "All" as the unsat core
        if sat is None:
            return ["All"]

        self.write("(get-unsat-core)\n")
        self.flush()

        return self.readline().replace('(', '').replace(')', '').split(' ')
