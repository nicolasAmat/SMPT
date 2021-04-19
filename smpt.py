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
__version__ = "3.0.0"

import argparse
import logging as log
import queue
import subprocess
import sys
import tempfile
import time

from parallelizer import Parallelizer
from properties import Formula, Properties
from ptnet import PetriNet
from system import System


def main():
    """ Main function.
    """
    # Start time
    start_time = time.time()

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
                        help='path to Petri Net (.net or .pnml format)')

    parser.add_argument('--colored',
                               action='store_true',
                               help='colored input Petri net')

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

    group_timeout = parser.add_mutually_exclusive_group()

    group_timeout.add_argument('--timeout',
                        action='store',
                        dest='timeout',
                        type=int,
                        default=225,
                        help='a limit per property on execution time')

    group_timeout.add_argument('--global-timeout',
                        action='store',
                        dest='global_timeout',
                        type=int,
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

    colored, path_pnml = False, None

    # Check if colored net
    if results.colored:
        colored = True
        path_ptnet = tempfile.NamedTemporaryFile().name
        subprocess.run(["mcc", "smpt", "-i", results.path_ptnet, '-o', path_ptnet])
        print(' '.join(["mcc", "smpt", "-i", results.path_ptnet, '-o', path_ptnet]))
        results.path_ptnet = path_ptnet + '.net'

    # Check if extension is `.pnml`
    elif results.path_ptnet.lower().endswith('.pnml'):
        path_pnml = results.path_ptnet
        results.path_ptnet = tempfile.NamedTemporaryFile(suffix='.net').name
        subprocess.run(["ndrio", path_pnml, results.path_ptnet])

    # Read the input Petri net
    ptnet = PetriNet(results.path_ptnet, path_pnml, colored)

    # By default no reduction
    ptnet_reduced = None
    system = None

    # Reduce the Petri net if '--auto-reduce' enabled
    if results.auto_reduce:
        if results.save_reduced_net:
            fp_ptnet_reduced = open(results.path_ptnet.replace('.net', '_reduced.net'), 'w+')
        else:
            fp_ptnet_reduced = tempfile.NamedTemporaryFile(suffix='.net')
        reduce_start_time = time.time()
        subprocess.run(
            ["reduce", "-rg,redundant,compact+,mg,4ti2", "-redundant-limit", "650", "-redundant-time", "10", "-inv-limit", "1000", "-inv-time", "10", results.path_ptnet, fp_ptnet_reduced.name])
        reduce_time = time.time() - reduce_start_time
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
    # TODO: whitelist instead of blacklist
    methods = []
    if not results.no_bmc:
        methods.append('BMC')
    if not results.no_ic3:
        methods.append('IC3')

    # Display net informations
    ptnet_info = '#' + ptnet.id
    if results.display_reduction_ratio and ptnet_reduced is not None:
        ptnet_info += " RR~{}%".format(int((len(ptnet.places) - len(ptnet_reduced.places)) / len(ptnet.places) * 100))
    if results.display_time and results.auto_reduce:
        ptnet_info += " t~{}s".format(reduce_time)
    if results.display_reduction_ratio or results.display_time:
        print(ptnet_info)

    # Disable reduction is the Petri net is not reducible
    if system is not None and not system.equations:
        ptnet_reduced = None
        system = None

    # Set timeout value
    if results.global_timeout is not None:
        timeout = results.global_timeout / len(properties.formulas)
        global_timeout = results.global_timeout
    else:
        timeout = results.timeout
        global_timeout = timeout * len(properties.formulas)

    # Iterate over properties
    computations = queue.Queue()
    for property_id, formula in properties.formulas.items():
        computations.put((property_id, formula))

    # Counter, number of propeties to be runned for the first pass
    counter, nb_properties = 0, computations.qsize()

    while not computations.empty() and time.time() - start_time < global_timeout:

        # Update the number of properties and the timeout for the next passes
        if counter > nb_properties:
            counter, nb_properties = 0, len(computations)
            timeout = (global_timeout - (time.time() - start_time)) / nb_properties

        property_id, formula = computations.get()

        methods = []

        if results.path_markings is not None:
            methods.append('ENUM')

        # Check non-monotonic analysis
        if results.skip_non_monotonic and formula.non_monotonic:
            print('FORMULA', property_id, 'SKIPPED')

        else:

            if ptnet_reduced is None or (ptnet_reduced is not None and len(ptnet_reduced.places)):
                # Use BMC and IC3 methods in parallel
                methods += ['BMC', 'PDR-REACH']
                
                if not formula.non_monotonic:
                    methods.append('PDR-COV')

            else:
                # Run SMT / CP methods
                methods = ['SMT', 'CP']

        # Run methods in parallel and get results
        parallelizer = Parallelizer(property_id, ptnet, formula, ptnet_reduced, system, results.display_method, results.display_time, results.display_model, results.debug, methods)

        # If computation is uncomplete add it to the queue
        if not parallelizer.run(timeout) and results.global_timeout is not None:
            computations.put((property_id, formula))

        # Stop computations
        parallelizer.stop()

        # Increment counter
        counter += 1

    # Close temporary files
    if results.auto_reduce:
        fp_ptnet_reduced.close()
    if results.auto_enumerative:
        fp_markings.close()


if __name__ == '__main__':
    main()
    sys.exit(0)
