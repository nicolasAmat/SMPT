#!/usr/bin/env python3

"""
CP: Constraint Programming Method

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

import logging as log

from solver import MiniZinc, Solver
from utils import STOP, send_signal


class CP:
    """
    Constraint Programming method.
    """

    def __init__(self, ptnet, formula, system, show_model=False, debug=False, minizinc=False):
        """ Initializer.
        """
        self.ptnet = ptnet

        self.formula = formula

        self.system = system
        
        self.show_model = show_model
        self.minizinc = minizinc

        if minizinc:
            self.solver = MiniZinc(debug)
        else:
            self.solver = Solver(debug)

    def prove(self, results, concurrent_pids):
        """ Prover.
        """
        model = None

        if self.minizinc:
            sat = self.prove_minizinc()
        else:
            sat = self.prove_smt()

        if sat and self.show_model:
            model = self.solver.get_model(self.ptnet)

        results.put([sat, model])

        # Kill the solver
        self.solver.kill()

        # Terminate concurrent methods
        if not concurrent_pids.empty():
            send_signal(concurrent_pids.get(), STOP)

    def prove_minizinc(self):
        """ Solve constraints using MiniZinc.
        """
        log.info("[CP] \t>> Set bound")
        self.solver.set_bound()
        log.info("[CP] \t>> Declaration of the places from the initial Petri net")
        self.solver.write(self.ptnet.minizinc_declare_places())
        log.info("[CP] \t>> Declaration of the additional variables and assertion of the reduction equations")
        self.solver.write(self.system.minizinc())
        log.info("[CP] \t>> Formula to check the satisfiability")
        self.solver.write(self.formula.R.minizinc(assertion=True))

        return self.solver.check_sat()

    def prove_smt(self):
        """ Solve constraints using SMT.
        """
        log.info("[CP] \t>> Declaration of the places from the initial Petri net")
        self.solver.write(self.ptnet.smtlib_declare_places())
        log.info("[CP] \t>> Declaration of the additional variables and assertion of the reduction equations")
        self.solver.write(self.system.smtlib())
        log.info("[CP] \t>> Formula to check the satisfiability")
        self.solver.write(self.formula.R.smtlib(assertion=True))

        return self.solver.check_sat()


if __name__ == '__main__':
    # TODO
    pass
