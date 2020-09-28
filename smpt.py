#!/usr/bin/env python3

"""
SMPT: Satisfiability Modulo Petri Net

An SMT-based model-checker that takes advantage of nets reduction.

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

import argparse
import logging as log
import subprocess
import tempfile
import time
from sys import exit

from enumerative import Enumerative
from parallelizer import Parallelizer
from properties import Formula, Properties
from ptnet import PetriNet
from system import System


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='SMPT: Satisfiability Modulo Petri Net')

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 1.0.0',
                        help="show the version number and exit")

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        help="increase output verbosity")

    parser.add_argument('--debug',
                        action='store_true',
                        help="print the SMT-LIB input/ouput")

    parser.add_argument('path_ptnet',
                        metavar='ptnet',
                        type=str,
                        help='path to Petri Net (.net format)')

    group_formula = parser.add_mutually_exclusive_group()

    group_formula.add_argument('--xml',
                               action='store',
                               dest='path_properties',
                               type=str,
                               help='use XML format for properties')

    group_formula.add_argument('--deadlock',
                               action='store_true',
                               help='deadlock analysis')

    group_formula.add_argument('--quasi-liveness',
                               action='store',
                               dest='quasi_live_transitions',
                               type=str,
                               help='liveness analysis (comma separated list of transition names)')

    group_formula.add_argument('--reachability',
                               action='store',
                               dest='reachable_places',
                               type=str,
                               help='reachibility analysis (comma separated list of place names)')

    group_reduce = parser.add_mutually_exclusive_group()

    group_reduce.add_argument('--auto-reduce',
                              action='store_true',
                              help="reduce automatically the Petri Net (using `reduce`)")

    group_reduce.add_argument('--reduced',
                              action='store',
                              dest='path_ptnet_reduced',
                              type=str,
                              help='path to reduced Petri Net (.net format)')

    group_enumerative = parser.add_mutually_exclusive_group()

    group_enumerative.add_argument('--auto-enumerative',
                                   action='store_true',
                                   help="enumerate automatically the states (using `tina`)")

    group_enumerative.add_argument('--enumerative',
                                   action='store',
                                   dest='path_markings',
                                   type=str,
                                   help='path to the state-space (.aut format)')

    parser.add_argument('--timeout',
                        action='store',
                        dest='timeout',
                        type=int,
                        default=60,
                        help='a limit on execution time')

    parser.add_argument('--display-model',
                        action='store_true',
                        help="display a counterexample if there is one")

    parser.add_argument('--display-time',
                        action='store_true',
                        help="display execution times")

    parser.add_argument('--display-reduction-ratio',
                        action='store_true',
                        help="display the reduction ratio")

    results = parser.parse_args()

    # Set the verbose level
    if results.verbose:
        log.basicConfig(format="%(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(message)s")

    # Read the input Petri net
    ptnet = PetriNet(results.path_ptnet)

    ptnet_reduced = None
    system = None

    # Reduce the Petri net if '--auto-reduce' enabled
    if results.auto_reduce:
        fp_ptnet_reduced = tempfile.NamedTemporaryFile(suffix='.net')
        start_time = time.time()
        subprocess.run(
            ["reduce", "-rg,redundant,compact+,convert,mg,4ti2,transitions", "-redundant-limit", "650", "-redundant-time", "10", "-inv-limit", "1000", "-inv-time", "10", results.path_ptnet, fp_ptnet_reduced.name])
        reduction_time = time.time() - start_time
        results.path_ptnet_reduced = fp_ptnet_reduced.name

    # Read the reduced Petri net and the system of equations linking both nets 
    if results.path_ptnet_reduced is not None:
        ptnet_reduced = PetriNet(results.path_ptnet_reduced)
        system = System(results.path_ptnet_reduced, ptnet.places.keys(), ptnet_reduced.places.keys())

    # Generate the state-space if '--auto-enumerative' enabled
    if results.auto_enumerative:
        fp_markings = tempfile.NamedTemporaryFile(suffix='.aut')
        if results.path_ptnet_reduced is not None:
            path_ptnet = results.path_ptnet_reduced
        else:
            path_ptnet = results.path_ptnet
        subprocess.run(["tina", "-aut", "-sp", "2", path_ptnet, fp_markings.name])
        results.path_markings = fp_markings.name

    # Read properties
    properties = Properties(ptnet, results.path_properties)

    # Generate a deadlock property if '--deadlock' enabled
    if results.deadlock:
        property_id = "Deadlock"
        formula = Formula(ptnet)
        formula.generate_deadlock()
        properties.add_formula(formula, property_id)

    # Generate a quasi-liveness property if '--quasi-liveness' enabled
    if results.quasi_live_transitions is not None:
        property_id = "Quasi-liveness-{}".format(results.quasi_live_transitions)
        transitions = results.quasi_live_transitions.replace('#', '').replace('{', '').replace('}', '').split(',')
        formula = Formula(ptnet)
        formula.generate_quasi_liveness(transitions)
        properties.add_formula(formula, property_id)

    # Generate a reachability property if '--reachability' enabled
    if results.reachable_places is not None:
        property_id = "Reachability:-{}".format(results.reachable_places)
        places = results.reachable_places.replace('#', '').replace('{', '').replace('}', '').split(',')
        marking = {ptnet.places[pl]: 1 for pl in places}
        formula = Formula(ptnet)
        formula.generate_reachability(marking)
        properties.add_formula(formula, property_id)

    # Display net informations
    ptnet_info = '#' + ptnet.id
    if results.display_reduction_ratio and ptnet_reduced is not None:
        ptnet_info += " RR~{}%".format(int((len(ptnet.places) - len(ptnet_reduced.places)) / len(ptnet.places) * 100))
    if results.display_time and ptnet_reduced is not None:
        ptnet_info += " t~{}s".format(reduction_time)
    print(ptnet_info)

    # Iterate over properties
    for property_id, formula in properties.formulas.items():
        print(property_id, end=' ')

        if results.path_markings is not None:
            # Use enumerative method
            result = []
            enumerative = Enumerative(results.path_markings, ptnet, formula, ptnet_reduced, system, results.debug)
            enumerative.prove(result)
            print(formula.result(result[0]))
            if len(result) > 1:
                result[1].display_model()
        else:
            # Use BMC and IC3 methods in parallel
            parallelizer = Parallelizer(ptnet, formula, ptnet_reduced, system, results.debug)
            sat, model, execution_time = parallelizer.run(results.timeout)
            # Display analysis result
            if sat is not None:
                print(formula.result(sat), end=' ')
            else:
                print("TIMEOUT", end=' ')
            # Display execution time
            if results.display_time:
                print(execution_time, end=' ')
            print()
            # Display model if there is one
            if results.display_model and model is not None:
                model.display_model()

    # Close temporary files
    if results.auto_reduce:
        fp_ptnet_reduced.close()
    if results.auto_enumerative:
        fp_markings.close()


if __name__ == '__main__':
    main()
    exit(0)
