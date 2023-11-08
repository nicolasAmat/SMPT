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
__version__ = "5.0"

from argparse import ArgumentParser
from itertools import repeat
from logging import DEBUG, basicConfig
from math import ceil
from multiprocessing import Process
from multiprocessing.pool import ThreadPool
from os import fsync, remove
from queue import Queue
from subprocess import run
from sys import exit
from tempfile import NamedTemporaryFile
from time import time
from typing import Optional

from smpt.exec.parallelizer import Parallelizer, worker
from smpt.interfaces.convert import convert
from smpt.interfaces.hwalk import hwalk
from smpt.interfaces.reduce import reduce
from smpt.interfaces.unfold import skeleton, unfold
from smpt.ptio.formula import Properties
from smpt.ptio.ptnet import PetriNet
from smpt.ptio.system import System


def main():
    """ Main function.
    """
    # Start time
    start_time = time()

    # Arguments parser
    parser = ArgumentParser(description='SMPT: Satisfiability Modulo Petri Net')

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 5.0',
                        help="show the version number and exit")

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        help="increase output verbosity")

    parser.add_argument('--debug',
                        action='store_true',
                        help="print the SMT-LIB input/output")

    parser.add_argument('-n', '--net',
                        metavar='ptnet',
                        type=str,
                        required=True,
                        help='path to Petri Net (.net or .pnml format)')

    parser.add_argument('--colored',
                        action='store_true',
                        help='colored input Petri net')

    group_properties = parser.add_mutually_exclusive_group()

    group_properties.add_argument('--xml',
                                  action='store',
                                  dest='path_properties',
                                  type=str,
                                  help='path to reachability formulas (.xml format)')

    parser.add_argument('--fireability',
                        action='store_true',
                        help="Reachability Fireability mode (Cardinality by default)")

    group_properties.add_argument('--ltl-file',
                                  action='store',
                                  dest='path_ltl_formula',
                                  type=str,
                                  help='path to reachability formula (.ltl format)')

    group_properties.add_argument('--ltl',
                                  action='store',
                                  dest='ltl_formula',
                                  type=str,
                                  help='reachability formula (.ltl format)')

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
                                  help='reachability analysis (comma separated list of place names)')

    parser.add_argument('--select-queries',
                                  action='store',
                                  dest='queries',
                                  type=str,
                                  help='verify queries of a given comma-separated list')

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

    group_methods = parser.add_mutually_exclusive_group(required=True)

    methods = ['WALK', 'STATE-EQUATION', 'INDUCTION', 'BMC', 'K-INDUCTION',
               'PDR-COV', 'PDR-REACH', 'PDR-REACH-SATURATED', 'SMT', 'CP', 'DUMMY']

    group_methods.add_argument('--methods',
                               default=methods,
                               nargs='*',
                               choices=methods,
                               help='enable methods among {}'.format(' '.join(methods)))

    group_methods.add_argument('--auto-enumerative',
                               action='store_true',
                               help="enumerate automatically the states (using `tina`)")

    group_methods.add_argument('--enumerative',
                               action='store',
                               dest='path_markings',
                               type=str,
                               help='path to the state-space (.aut format)')

    parser.add_argument('--project',
                        action='store_true',
                        help='Use TFG projection for WALK, BMC, K-INDUCTION, PDR, STATE-EQUATION')
    
    parser.add_argument('--drop-incomplete',
                        action='store_true',
                        help='Drop non shadow-complete projections')

    parser.add_argument('--projection-timeout',
                        action='store',
                        dest='projection_timeout',
                        type=int,
                        default=3,
                        help='a limit on projection time (per formula)')

    parser.add_argument('--show-projection',
                        action='store_true',
                        help='Show projected formulas')

    parser.add_argument('--save-projection',
                        action='store',
                        dest='path_projection_directory',
                        type=str,
                        help='Save projected formulas')

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

    parser.add_argument('--show-techniques',
                        action='store_true',
                        help="show the method returning the result")

    parser.add_argument('--show-time',
                        action='store_true',
                        help="show the execution time")

    parser.add_argument('--show-reduction-ratio',
                        action='store_true',
                        help="show the reduction ratio")

    parser.add_argument('--show-shadow-completeness',
                        action='store_true',
                        help="show the shadow completeness")

    parser.add_argument('--show-model',
                        action='store_true',
                        help="show a counterexample if there is one")

    parser.add_argument('--check-proof',
                        action='store_true',
                        help="check and show the certificate of invariance if there is one")

    parser.add_argument('--export-proof',
                        action='store',
                        dest='path_proof',
                        type=str,
                        help='export the proof of invariance if there is one')

    parser.add_argument('--mcc',
                        action='store_true',
                        help="Model Checking Contest mode")

    results = parser.parse_args()

    print("# Hello")

    # Set the verbose level
    if results.verbose:
        basicConfig(format="%(message)s", level=DEBUG)
    else:
        basicConfig(format="%(message)s")

    # Path to Petri net (can evolved if some file conversion are necessary)
    path_net = results.net

    # Path to .pnml Petri net (do no include colored nets)
    path_pnml = None

    # Use .pnml for reduction (if ndrio failed)
    use_pnml_reduce = False

    # Check if colored net
    ptnet_skeleton = None
    answered: set[str] = set()

    if results.colored:
        remaining_queries: Optional[list[int]] = None
        
        if results.mcc and not results.fireability:
            # If not fireability: INITIAL-MARKING and STATE-EQUATION on skeleton
            path_skeleton = skeleton(path_net)

            if path_skeleton is not None:
                # Skeleton Petri net and properties
                ptnet_skeleton = PetriNet(path_skeleton, skeleton=True, state_equation=True)
                properties = Properties(None, ptnet_skeleton=ptnet_skeleton, xml_filename=results.path_properties, simplify=True)
                
                # Initial marking and state-equation
                pool = ThreadPool(processes=2)
                parallelizers = [Parallelizer(properties, property_id, None, formula, ['INITIAL-MARKING', 'STATE-EQUATION'], ptnet_skeleton=ptnet_skeleton, show_techniques=results.show_techniques, show_time=results.show_time, show_model=results.show_model, debug=results.debug) for property_id, formula in properties.formulas.items()]
                pre_results = pool.starmap(worker, zip(parallelizers, repeat(int((results.global_timeout - (time() - start_time)) / 16) if results.global_timeout else results.timeout)))

                # Compute answered queries (set of property ids) and remaining queries (list of indices)
                remaining_queries = []
                for index, (property_id, formula) in enumerate(properties.formulas.items()):
                    if property_id in pre_results:
                        answered.add(property_id)
                    if pre_results is None or property_id not in pre_results:
                        remaining_queries.append(index)

                # If no remaining queries then exit
                if not remaining_queries:
                    print("# Bye bye")
                    exit()

        # Hwalk (before unfolding for both fireability and cardinality)
        if results.mcc:
            answered |= hwalk(path_net, results.path_properties, select_queries=remaining_queries)
            if len(answered) == 16:
                print("# Bye bye")
                exit()

        path_net = unfold(path_net)
        if path_net is None:
            print("# Bye bye")
            exit()

    # If not colored check if extension is `.pnml`
    elif path_net.lower().endswith('.pnml'):
        path_pnml = path_net
        path_net, use_pnml_reduce = convert(path_pnml)

    # State equation method enabled
    state_equation = results.mcc or any(method in ['STATE-EQUATION', 'K-INDUCTION', 'PDR-COV', 'PDR-REACH', 'PDR-REACH-SATURATED'] for method in results.methods)

    # Parikh computation enabled
    parikh = results.mcc or ('STATE-EQUATION' in results.methods and 'WALK' in results.methods)

    # Read the input Petri net
    ptnet = PetriNet(path_net, pnml_filename=path_pnml, colored=results.colored, state_equation=state_equation, parikh=parikh) if path_net else None

    # By default no reduction
    ptnet_reduced, system, ptnet_tfg = None, None, None

    # List of reduce processes
    reduce_processes = []

    # Reduce source
    reduce_source = path_pnml if use_pnml_reduce else path_net

    # Reduce the Petri net if '--auto-reduce' enabled
    path_ptnet_reduced = results.path_ptnet_reduced if ptnet is not None else None
    fp_ptnet_reduced = None
    if ptnet is not None and results.auto_reduce and path_ptnet_reduced is None:
        extension = '.pnml' if path_pnml else '.net'
        fp_ptnet_reduced = open(results.net.replace(extension, '_reduced.net'), 'w+') if results.save_reduced_net else NamedTemporaryFile(suffix='.net', delete=False)
        path_ptnet_reduced = fp_ptnet_reduced.name
        reduce_processes.append(Process(target=reduce, args=(reduce_source, path_ptnet_reduced, False, results.show_time,)))
        reduce_processes[-1].start()

    # Reduce the Petri net using TFG reductions if `--project` enabled
    fp_ptnet_tfg = None
    if ptnet is not None and results.project:
        extension = '.pnml' if path_pnml else '.net'
        fp_ptnet_tfg = open(results.net.replace(extension, '_tfg.net'), 'w+') if results.save_reduced_net else NamedTemporaryFile(suffix='.net', delete=False)
        path_ptnet_tfg = fp_ptnet_tfg.name
        reduce_processes.append(Process(target=reduce, args=(reduce_source, path_ptnet_tfg, True, results.show_time,)))
        reduce_processes[-1].start()

    # Join reduce processes
    for proc in reduce_processes:
        proc.join()

    # Fsync
    if fp_ptnet_reduced is not None:
        fsync(fp_ptnet_reduced.fileno())
        fp_ptnet_reduced.close()
    if fp_ptnet_tfg is not None:
        fsync(fp_ptnet_tfg.fileno())
        fp_ptnet_tfg.close()
    
    # Read the reduced Petri net and the system of reduction equations
    fully_reducible = False
    if path_ptnet_reduced is not None:
        ptnet_reduced = PetriNet(path_ptnet_reduced, state_equation=state_equation)
        system = System(path_ptnet_reduced, ptnet.places.keys(), ptnet_reduced.places.keys())
        # Set fully reducible flag
        fully_reducible = not ptnet_reduced.places
    
    # Read the reduced Petri net using TFG reductions
    if results.project and not (results.mcc and fully_reducible):
        ptnet_tfg = PetriNet(path_ptnet_tfg, state_equation=state_equation)

    # Show net information
    if results.show_reduction_ratio:
        if ptnet_reduced is not None:
            print("# Reduction ratio (Full) ~ {}%".format(int((len(ptnet.places) - len(ptnet_reduced.places)) / len(ptnet.places) * 100)))
        if ptnet_tfg is not None:
            print("# Reduction ratio (TFG) ~ {}%".format(int((len(ptnet.places) - len(ptnet_tfg.places)) / len(ptnet.places) * 100)))

    # Disable reduction if the Petri net is not reducible
    if system is not None and not system.equations:
        ptnet_reduced = None
        system = None

    # Disable TFG if the Petri net is not reducible
    if ptnet_tfg is not None and len(ptnet_tfg.places) == len(ptnet.places):
        ptnet_tfg = None

    # Generate the state-space if '--auto-enumerative' enabled
    if results.auto_enumerative:
        fp_markings = NamedTemporaryFile(suffix='.aut', delete=False)
        if path_ptnet_reduced is not None:
            net = path_ptnet_reduced
        else:
            net = results.net
        run(["tina", "-aut", "-sp", "2", net, fp_markings.name])
        results.path_markings = fp_markings.name
        fsync(fp_markings.fileno())
        fp_markings.close()

    # Read properties and keep skeleton ones in not fully reducible
    properties = Properties(ptnet, ptnet_tfg=ptnet_tfg, xml_filename=results.path_properties, fireability=results.fireability, simplify=results.mcc and not results.queries, answered=answered)

    # Parse .ltl file if there is one
    if results.path_ltl_formula:
        with open(results.path_ltl_formula, 'r') as fp_ltl:
            properties.add_ltl_formula(fp_ltl.read().strip())

    # Parse .ltl formula if there is one
    if results.ltl_formula:
        properties.add_ltl_formula(results.ltl_formula)

    # Generate a deadlock property if '--deadlock' enabled
    if results.deadlock:
        properties.add_deadlock_formula()

    # Generate a quasi-liveness property if '--quasi-liveness' enabled
    if results.quasi_live_transitions is not None:
       properties.add_quasi_live_formula(results.quasi_live_transitions)

    # Generate a reachability property if '--reachability' enabled
    if results.reachable_places is not None:
        properties.add_reachability_formula(results.reachable_places)

    # Filter queries if option enabled
    if results.queries:
        properties.select_queries(results.queries)

    # Free useless data
    if ptnet is not None:
        ptnet.free_mappings()

    # Check tautologies
    if results.mcc:
        for (property_id, verdict) in properties.tautologies():
            print("\nFORMULA {} {} TECHNIQUES TAUTOLOGY".format(property_id, verdict))

    # Generate Walk files if mcc mode, projection or Walk methods enabled
    if results.mcc or (ptnet_tfg is not None and results.project) or 'WALK' in results.methods:
        properties.generate_walk_files()

    # Project formulas if enabled
    if results.project and ptnet_tfg is not None and not (results.mcc and fully_reducible):
        properties.project(ptnet_tfg, drop_incomplete=results.mcc or results.drop_incomplete, timeout=results.projection_timeout, show_projection=results.show_projection, save_projection=results.path_projection_directory, show_time=results.show_time, show_shadow_completeness=results.show_shadow_completeness, debug=results.debug)
        for (property_id, verdict) in properties.tautologies(projection=True):
            print("\nFORMULA {} {} TECHNIQUES STRUCTURAL-REDUCTION PROJECTION TAUTOLOGY".format(property_id, verdict))

    # Exit if no formula anymore
    if not properties.formulas:
        print("# Bye bye")
        exit()

    # Generate Parikh files
    if parikh:
        properties.generate_parikh_files()

    # Set timeout value
    if results.global_timeout is not None:
        timeout = int((results.global_timeout - (time() - start_time)) / len(properties.formulas))
        global_timeout = results.global_timeout
    else:
        timeout = results.timeout
        global_timeout = timeout * len(properties.formulas)

    # MCC pre-computation
    pre_results = None
    if results.mcc and not fully_reducible:
        try:
            pool = ThreadPool(processes=2)
            parallelizers = [Parallelizer(properties, property_id, ptnet, formula, ['WALK-NO-PARIKH', 'STATE-EQUATION'], ptnet_reduced=ptnet_reduced, system=system, ptnet_tfg=ptnet_tfg, projected_formula=properties.projected_formulas.get(property_id, None), show_techniques=results.show_techniques, show_time=results.show_time, show_model=results.show_model, debug=results.debug, mcc=True, pre_run=True) for property_id, formula in properties.formulas.items()]
            pre_results = pool.starmap(worker, zip(parallelizers, repeat(timeout)))
        finally:
            pool.close()
            pool.join()

    # Free nupn
    if ptnet is not None:
        ptnet.free_nupn()

    # Iterate over properties
    computations = Queue()
    nb_remaining_properties = 0
    for property_id, formula in properties.formulas.items():
        if pre_results is None or property_id not in pre_results:
            computations.put((property_id, formula))
            nb_remaining_properties += 1

    # Number of properties to be run, timeout and counter
    nb_properties = nb_remaining_properties
    timeout = (global_timeout - (time() - start_time)) / nb_properties if nb_remaining_properties else None
    counter = 0

    while not computations.empty() and time() - start_time < global_timeout:

        # Update the timeout
        if counter >= nb_properties:
            timeout = ceil((global_timeout - (time() - start_time)) / nb_remaining_properties)

        # Get property
        property_id, formula = computations.get()

        # List of methods
        methods = []

        # Methods management are very different in mcc mode
        if not results.mcc:
            # Add ENUM method if markings were generated
            if results.path_markings is not None:
                methods.append('ENUM')

            # Check non-monotonic analysis
            if results.skip_non_monotonic and formula.non_monotonic:
                print('FORMULA', property_id, 'SKIPPED')

            else:
                methods += ['WALK', 'STATE-EQUATION', 'INDUCTION', 'BMC', 'K-INDUCTION', 'PDR-REACH', 'PDR-REACH-SATURATED']

                if not formula.non_monotonic:
                    methods.append('PDR-COV')
                    
                if fully_reducible:
                    # Run SMT / CP methods
                    methods += ['SMT', 'CP']

            # Keep only enabled methods
            methods = list(set(methods) & set(results.methods))

            # Add BMC if K-INDUCTION enabled
            if 'K-INDUCTION' in methods and 'BMC' not in methods:
                methods.append('BMC')
        else:
            # Methods for second round differ
            if counter < nb_properties:
                # Add three walkers when fully reducible and mcc mode enabled
                if ptnet_reduced and not ptnet_reduced.places:
                    methods = ['SMT'] + ['WALK' for _ in range(3)]
                else:
                    methods = ['WALK', 'BMC', 'K-INDUCTION', 'BULK-PDR-COMPOUND-WALK']
            else:
                # If second round then run only walkers (and BULK without PDR)
                methods = ['WALK', 'WALK', 'WALK-NO-PARIKH', 'BULK-COMPOUND-WALK']

        # Run methods in parallel and get results
        parallelizer = Parallelizer(properties, property_id, ptnet, formula, methods, ptnet_reduced=ptnet_reduced, system=system, ptnet_tfg=ptnet_tfg, projected_formula=properties.projected_formulas.get(property_id, None), show_techniques=results.show_techniques, show_time=results.show_time, show_model=results.show_model, debug=results.debug, path_markings=results.path_markings, check_proof=results.check_proof, path_proof=results.path_proof, mcc=results.mcc, pre_run=(counter >= nb_properties))

        # If computation is uncompleted add it to the queue
        if parallelizer.run(timeout) is None and results.global_timeout is not None:
            computations.put((property_id, formula))
        else:
            nb_remaining_properties -= 1

        counter += 1

    # Close temporary files
    if results.net.endswith('.pnml'):
        remove(path_net)
    if results.auto_reduce:
        fp_ptnet_reduced.close()
        if not results.save_reduced_net:
            remove(fp_ptnet_reduced.name)
    if results.project:
        fp_ptnet_tfg.close()
        if not results.save_reduced_net:
            remove(fp_ptnet_tfg.name)
    if results.auto_enumerative:
        fp_markings.close()
        remove(fp_markings.name)

    # Remove Parikh files if enabled
    if parikh:
        properties.remove_parikh_files()

    # Remove Walk files if Walk or mcc mode enabled
    if 'WALK' in results.methods or results.project or results.mcc:
        properties.remove_walk_files()

    print("# Bye bye")


if __name__ == '__main__':
    main()
