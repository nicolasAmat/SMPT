#!/usr/bin/env python3

"""
Satisfiability Modulo Petri Net
"""

from pn import PetriNet
from formula import Properties
from eq import System
from enumerativemarking import EnumerativeMarking
from kinduction import KInduction

import argparse
import os
import subprocess
from threading import Thread, Event
import logging as log

stop_it = Event()

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
    print("Satisfiability Modulo PeTri Net")
    print("LAAS-CNRS")
    exit(0)

def enumerative_marking(pn, pn_reduced, eq, formula, path_markings):
    """
    Enumerative method caller
    """
    markings = EnumerativeMarking(path_markings, pn, pn_reduced, eq, formula)
    markings.prove()

def k_induction(pn, pn_reduced, eq, formula):
    """
    K-induction method caller
    """
    k_induction = KInduction(pn, pn_reduced, eq, formula)

    # Run solver with timeout
    proc = Thread(target= k_induction.prove)
    proc.start()
    proc.join(timeout = 5)
    stop_it.set()

def main():
    """
    Main Function
    """
    parser = argparse.ArgumentParser(description='Satisfiability Modulo Petri Net')
    
    parser.add_argument('--about',
                        action='store_true',
                        help="dev information")

    parser.add_argument('--version',
                        action='version',
                        version='%(prog)s 1.0')

    parser.add_argument('-v', '--verbose',
                        action='store_true',
                        help="increase output verbosity")
    
    parser.add_argument('path_pn',
                        metavar='pn',
                        type=str,
                        help='path to Petri Net (.net format)')

    parser.add_argument('path_props',
                        metavar='properties',
                        type=str,
                        help='path to Properties (.xml format)')

    parser.add_argument('--reduced',
                        action='store',
                        dest='path_pn_reduced',
                        type=str,
                        help='Path to reduced Petri Net (.net format)')

    parser.add_argument('--enumerative',
                        action='store',
                        dest='path_markings',
                        type=str,
                        help='Path to markings  (.aut format)')

    results = parser.parse_args()

    if results.verbose:
        log.basicConfig(format="%(message)s", level=log.DEBUG)
    else:
        log.basicConfig(format="%(message)s")

    if results.about:
        about()

    pn = PetriNet(results.path_pn)
    
    if results.path_pn_reduced is not None:
        pn_reduced = PetriNet(results.path_pn_reduced)
        eq = System(results.path_pn_reduced, pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = PetriNet(results.path_pn)
        eq = System(results.path_pn, pn.places.keys(), pn_reduced.places.keys())

    props = Properties(pn, results.path_props)

    for formula_id, formula in props.formulas.items():
        print("---{}---".format(formula_id))
        if results.path_markings is not None:
            enumerative_marking(pn, pn_reduced, eq, formula, results.path_markings)
        else:
            k_induction(pn, pn_reduced, eq, formula)
    exit(0)


if __name__ == '__main__':
    main()