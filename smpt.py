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
import sys
import tempfile
import time

from cp import CP
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

    group_properties = parser.add_mutually_exclusive_group()

    group_properties.add_argument('--xml',
                               action='store',
                               dest='path_properties',
                               type=str,
                               help='use XML format for properties')

    group_properties.add_argument('--deadlock',
                               action='store_true',
                               help='deadlock analysis')

    group_properties.add_argument('--quasi-liveness',
                               action='store',
                               dest='quasi_live_transitions',
                               type=str,
                               help='liveness analysis (comma separated list of transition names)')

    group_properties.add_argument('--reachability',
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

    parser.add_argument('--save-reduced-net',
                               action='store_true',
                               help='save the reduced net')

    group_methods = parser.add_mutually_exclusive_group()

    group_methods.add_argument('--no-bmc',
                               action='store_true',
                               help='disable BMC method')

    group_methods.add_argument('--no-ic3',
                               action='store_true',
                               help='disable IC3 method')

    group_methods.add_argument('--auto-enumerative',
                                   action='store_true',
                                   help="enumerate automatically the states (using `tina`)")

    group_methods.add_argument('--enumerative',
                                   action='store',
                                   dest='path_markings',
                                   type=str,
                                   help='path to the state-space (.aut format)')

    group_methods.add_argument('--minizinc',
                                   action='store_true',
                                   help='use MiniZinc in case of fully reducible nets')

    parser.add_argument('--timeout',
                        action='store',
                        dest='timeout',
                        type=int,
                        default=60,
                        help='a limit on execution time')

    parser.add_argument('--skip-non-monotonic',
                        action='store_true',
                        help="skip non-monotonic properties")

    parser.add_argument('--display-method',
                        action='store_true',
                        help="display the method returning the result")

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

    # By default no reduction
    ptnet_reduced = None
    system = None

    # Reduce the Petri net if '--auto-reduce' enabled
    if results.auto_reduce:
        if results.save_reduced_net:
            fp_ptnet_reduced = open(results.path_ptnet.replace('.net', '_reduced.net'), 'w+')
        else:
            fp_ptnet_reduced = tempfile.NamedTemporaryFile(suffix='.net')
        start_time = time.time()
        subprocess.run(
            ["reduce", "-rg,redundant,compact+,mg,4ti2", "-redundant-limit", "650", "-redundant-time", "10", "-inv-limit", "1000", "-inv-time", "10", results.path_ptnet, fp_ptnet_reduced.name])
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
        property_id = "ReachabilityDeadlock"
        formula = Formula(ptnet)
        formula.generate_deadlock()
        properties.add_formula(formula, property_id)

    # Generate a quasi-liveness property if '--quasi-liveness' enabled
    if results.quasi_live_transitions is not None:
        property_id = "Quasi-liveness-{}".format(results.quasi_live_transitions)
        transitions = results.quasi_live_transitions.replace('#', '.').replace('{', '').replace('}', '').split(',')
        formula = Formula(ptnet)
        formula.generate_quasi_liveness(transitions)
        properties.add_formula(formula, property_id)

    # Generate a reachability property if '--reachability' enabled
    if results.reachable_places is not None:
        property_id = "Reachability:-{}".format(results.reachable_places)
        places = results.reachable_places.replace('#', '.').replace('{', '').replace('}', '').split(',')
        marking = {ptnet.places[pl]: 1 for pl in places}
        formula = Formula(ptnet)
        formula.generate_reachability(marking)
        properties.add_formula(formula, property_id)

    # Read the method restriction
    method_disabled = ''
    if results.no_ic3:
        method_disabled = 'IC3'
    if results.no_bmc:
        method_disabled = 'BMC'

    # Display net informations
    ptnet_info = '#' + ptnet.id
    if results.display_reduction_ratio and ptnet_reduced is not None:
        ptnet_info += " RR~{}%".format(int((len(ptnet.places) - len(ptnet_reduced.places)) / len(ptnet.places) * 100))
    if results.display_time and results.auto_reduce:
        ptnet_info += " t~{}s".format(reduction_time)
    print(ptnet_info)

    # Disable reduction is the Petri net is not reducible
    if system is not None and not system.equations:
        ptnet_reduced = None
        system = None

    # Iterate over properties
    for property_id, formula in properties.formulas.items():
        print(property_id, end=' ')

        if results.path_markings is not None:
            # Use enumerative method
            result = []
            enumerative = Enumerative(results.path_markings, ptnet, formula, ptnet_reduced, system, results.debug)
            enumerative.prove(result)
            print(formula.result(result[0]), end=' ')
            # Display method
            if results.display_method:
                print('ENNUMERATIVE', end= '')
            print()
            if len(result) > 1:
                result[1].display_model()
        else:
            # Check non-monotonic analysis
            if results.skip_non_monotonic and formula.non_monotonic:
                print("SKIPPED")
            else:
                if ptnet_reduced is not None and len(ptnet_reduced.places):
                    # Use BMC and IC3 methods in parallel
                    parallelizer = Parallelizer(ptnet, formula, ptnet_reduced, system, results.display_model, results.debug, method_disabled)
                    sat, model, execution_time, method = parallelizer.run(results.timeout)

                else:
                    # Use CP (Constraint Programming) method
                    cp = CP(ptnet, formula, system, results.timeout, results.display_model, results.debug, results.minizinc)
                    sat, model, execution_time = cp.prove()
                    method = "CP"

                # Display analysis result
                if sat is not None:
                    print(formula.result(sat), end=' ')
                else:
                    print("TIMEOUT", end=' ')

                # Display execution time
                if results.display_time:
                    print(execution_time, end=' ')

                # Display method
                if results.display_method:
                    if method != '':
                        print(method, end= ' ')
                    if ptnet_reduced.places and formula.non_monotonic:
                        print("(IC3_auto-disabled)", end='')
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
    sys.exit(0)
