#!/usr/bin/env python3

"""
Satisfiability Modulo Petri Net
"""

from pn import *
from formula import *
from eq import *
from marking import *

import sys
import os
import subprocess

def main(argv):
    if len(argv) < 3:
        exit("File missing: ./smpn <path_to_initial_petri_net> <path_to_reduce_net> <path_to_aut_file>")
    net = PetriNet(argv[1])
    reduced_net = PetriNet(argv[2])
    eq = System(argv[2], net.places.keys())
    phi = Formula(net)
    if len(argv) > 3:
        marks = Marking(argv[3], reduced_net)

    smtlib = "; Variable Definitions\n" \
        + net.smtlib() \
        + "; Reduction Equations\n" \
        + eq.smtlib() \
        + "; Property Formula\n" \
        + phi.smtlib() \
        + "; Reduced Net Markings\n" \
    
    if len(argv) > 3:    
        smtlib += "; Reduced Net Markings\n" \
            + marks.smtlib() 
    
    smtlib += "(check-sat)\n"

    print("Input into the SMT Solver")
    print("-------------------------")
    print(smtlib)

    smt_filename = "a.smt"
    smt_file = open(smt_filename, 'w')
    smt_file.write(smtlib)
    smt_file.close()
    proc = subprocess.Popen(['z3', '-smt2', smt_filename], stdout=subprocess.PIPE)
    
    if proc.stdout.readline().decode('utf-8').strip() != 'sat':
        sat = False
    else:		
        sat = True

    print("Result computed using z3")
    print("------------------------")
    phi.result(sat)

    proc.poll()
    os.remove(smt_filename)


if __name__=='__main__':
    main(sys.argv)
    