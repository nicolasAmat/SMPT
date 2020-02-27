#!/usr/bin/env python3

"""
Satisfiability Modulo Petri Net
"""

from pn import *
from formula import *
from eq import *

import sys

def main(argv):
    if (len(argv) != 3):
        exit("File missing: ./smpn <path_to_initial_petri_net> <path_to_reduce_net>")
    net = PetriNet(argv[1])
    eq = System(argv[2])
    phi = Formula(net)

    print("; Variable Definitions")
    print(net.smtlib())
    print("; Reduction Equations")
    print(eq.smtlib())
    print(", Property Formula")
    print(phi.smtlib())

if __name__=='__main__':
    main(sys.argv)
    