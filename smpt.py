#!/usr/bin/env python3

"""
Satisfiability Modulo Petri Net

LAAS-CNRS

Author: Nicolas AMAT
"""

from pn import PetriNet
from formula import Properties
from eq import System
from enumerativemarking import EnumerativeMarking
from kinduction import KInduction
from ic3 import IC3

import sys
import os
import argparse
import subprocess
import logging as log
from threading import Thread, Event

stop_it = Event()
timeout = 5

def about():
    """
    About printer
    """
    logo = "            _____                    _____                    _____                _____            \n" \
         + "           /\    \                  /\    \                  /\    \              /\    \           \n" \
         + "          /::\    \                /::\____\                /::\    \            /::\    \          \n" \
         + "         /::::\    \              /::::|   |               /::::\    \           \:::\    \         \n" \
         + "        /::::::\    \            /:::::|   |              /::::::\    \           \:::\    \        \n" \
         + "       /:::/\:::\    \          /::::::|   |             /:::/\:::\    \           \:::\    \       \n" \
         + "      /:::/__\:::\    \        /:::/|::|   |            /:::/__\:::\    \           \:::\    \      \n" \
         + "      \:::\   \:::\    \      /:::/ |::|   |           /::::\   \:::\    \          /::::\    \     \n" \
         + "    ___\:::\   \:::\    \    /:::/  |::|___|______    /::::::\   \:::\    \        /::::::\    \    \n" \
         + "   /\   \:::\   \:::\    \  /:::/   |::::::::\    \  /:::/\:::\   \:::\____\      /:::/\:::\    \   \n" \
         + "  /::\   \:::\   \:::\____\/:::/    |:::::::::\____\/:::/  \:::\   \:::|    |    /:::/  \:::\____\  \n" \
         + "  \:::\   \:::\   \::/    /\::/    / ~~~~~/:::/    /\::/    \:::\  /:::|____|   /:::/    \::/    /  \n" \
         + "   \:::\   \:::\   \/____/  \/____/      /:::/    /  \/_____/\:::\/:::/    /   /:::/    / \/____/   \n" \
         + "    \:::\   \:::\    \                  /:::/    /            \::::::/    /   /:::/    /            \n" \
         + "     \:::\   \:::\____\                /:::/    /              \::::/    /   /:::/    /             \n" \
         + "      \:::\  /:::/    /               /:::/    /                \::/____/    \::/    /              \n" \
         + "       \:::\/:::/    /               /:::/    /                  ~~           \/____/               \n" \
         + "        \::::::/    /               /:::/    /                                                      \n" \
         + "         \::::/    /               /:::/    /                                                       \n" \
         + "          \::/    /                \::/    /                                                        \n" \
         + "           \/____/                  \/____/                                                         \n"
    print(logo)
    print("\tSatisfiability Modulo PeTri Net")
    print("\t-------------------------------\n")
    print("LAAS-CNRS")
    print("Author: Nicolas AMAT")
    exit(0)

def enumerative_marking(path_markings, pn, formula, pn_reduced, eq):
    """
    Enumerative method caller
    """
    markings = EnumerativeMarking(path_markings, pn, formula, pn_reduced, eq)
    markings.prove()

def k_induction(pn, formula, pn_reduced, eq, debug):
    """
    K-induction method caller
    """
    k_induction = KInduction(pn, formula, pn_reduced, eq, debug)

    # Run solver with timeout
    proc = Thread(target= k_induction.prove)
    proc.start()
    proc.join(timeout = 5)
    stop_it.set()

def ic3(pn):
    """
    IC3 method caller
    """
    pass

def main():
    """
    Main Function
    """
    if len(sys.argv) == 2 and sys.argv[1] == '--about':
        about()

    parser = argparse.ArgumentParser(description='Satisfiability Modulo Petri Net')

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 1.0')

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        help="increase output verbosity")

    parser.add_argument('--debug',
                        action='store_true',
                        help="display the SMT-LIB input/ouput")
    
    parser.add_argument('path_pn',
                        metavar='pn',
                        type=str,
                        help='path to Petri Net (.net format)')

    parser.add_argument('path_props',
                        metavar='properties',
                        type=str,
                        help='path to Properties (.xml format)')

    group_reduce = parser.add_mutually_exclusive_group()
    
    group_reduce.add_argument('--auto-reduce',
                        action='store_true',
                        help="automatically reduces the Petri Net (using `reduce`)")

    group_reduce.add_argument('--reduced',
                        action='store',
                        dest='path_pn_reduced',
                        type=str,
                        help='path to reduced Petri Net (.net format)')

    group_enumerative = parser.add_mutually_exclusive_group()

    group_enumerative.add_argument('--auto-enumerative',
                        action='store_true',
                        help="automatically enumerates the states (using `tina`)")

    group_enumerative.add_argument('--enumerative',
                        action='store',
                        dest='path_markings',
                        type=str,
                        help='Path to markings  (.aut format)')

    parser.add_argument('--timeout',
                        action='store',
                        dest='value',
                        type=int,
                        help='configure the timeout')                    

    results = parser.parse_args()

    if results.verbose:
        log.basicConfig(format="%(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(message)s")

    pn = PetriNet(results.path_pn)
    
    if results.path_pn_reduced is not None:
        pn_reduced = PetriNet(results.path_pn_reduced)
        eq = System(results.path_pn_reduced, pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = None
        eq = None
    
    props = Properties(pn, results.path_props)

    for formula_id, formula in props.formulas.items():
        print("---{}---".format(formula_id))
        if results.path_markings is not None:
            enumerative_marking(results.path_markings, pn, formula, pn_reduced, eq)
        else:
            k_induction(pn, formula, pn_reduced, eq, results.debug)
    exit(0)


if __name__ == '__main__':
    main()