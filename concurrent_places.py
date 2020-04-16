#!/usr/bin/env python3

"""
Concurrent Places Analyzer.

Ref: Garavel, “Nested-Unit Petri Nets.”
"""

from pn import PetriNet, Place
from eq import System
from formula import Formula, Clause, Inequality
from k_induction import KInduction

import sys
from threading import Thread, Event

stop_it_concurrent_places = Event()


class ConcurrentPlaces:
    """ 
    Concurrent Places Analyzer.
    """

    def __init__(self, pn, formula, pn_reduced=None, eq=None, debug=None, compressed=True):
        """ Initializer.
        """
        self.pn = pn
        self.pn_reduced = pn_reduced
        self.eq = eq

        self.debug = debug

        self.formula = formula
        self.c = []

        self.matrix = None

    def analyze(self, timeout):
        """
        Run Concurrent Places Analysis using k-induction.
        """
        self.build_matrix()
        self.initialization()
        proc = Thread(target=self.iterate)
        proc.start()
        proc.join(timeout)
        stop_it_concurrent_places.set()

    def display(self, compressed=True):
        """
        Display Concurrent Places matrix.
        """
        if self.matrix is None:
            print("Cannot display the Concurrent Places matrix before analyze.")
            exit(0)
        if compressed:
            self.display_compressed_matrix()
        else:
            self.display_matrix()

    def build_matrix(self):
        """ Build a dictionary that create an order on the places.
        """
        self.matrix = [[0 for j in range(i + 1)] for i in range(self.pn.counter_places)]
        for i in range(self.pn.counter_places):
            self.matrix[i][i] = 1

    def initialization(self):
        """ Initialization.
            If at least two places in m0 are marked,
            C := {m0}
        """
        m_zero = []

        for pl in self.pn.places.values():
            if pl.marking > 0:
                m_zero.append(pl)
        
        if len(m_zero) > 1:
            self.add_clause(m_zero)

    def iterate(self):
        """ Iterate until it finds new markings m
            where at least two places are marked in it.
            C := C U {m}
        """
        while not stop_it_concurrent_places.is_set():

            k_induction = KInduction(self.pn, self.formula, self.pn_reduced, self.eq, self.debug)
            model = k_induction.prove(display=False)

            if model is None:
                return

            m = []
            for eq in model.inequalities:
                if eq.right_member > 0:
                    m.append(eq.left_member)
            
            self.add_clause(m)

    def add_clause(self, m):
        """ Block a marking m.
        """
        self.c.append(m)
        
        inequalities = []

        for pl in self.pn.places.values():
            if pl not in m:
                inequalities.append(Inequality(pl, 0, '>'))
        cl = Clause(inequalities, 'or')
        self.formula.clauses.append(cl)

        self.fill_matrix(m)

    def fill_matrix(self, m):
        """ Fill a marking m in the Concurrent Places matrix.
        """
        for index, pl1 in enumerate(m):
            for pl2 in m[index + 1:]:
                if pl1.order > pl2.order:
                    self.matrix[pl1.order][pl2.order] = 1 
                else:
                    self.matrix[pl2.order][pl1.order] = 1

    def display_matrix(self):
        """ Display Concurrent Places matrix.
            Half matrix, raw format.
        """
        for line in self.matrix:
            print(' '.join(map(str, line)))

    def compression_rle(self, elem, counter):
        """ Run-Length Encoding helper.
        """
        if counter < 4:
            return str(elem) * counter
        else:
            return "{}({})".format(elem, counter)

    def display_compressed_matrix(self):
        """ Display Concurrent Places matrix.
            Comrpessed format.
        """
        for line in self.matrix:
            text = ""
            for i in range(len(line)):
                elem = line[i]
                if i == 0:
                    previous = elem
                    counter = 0
                if i == len(line) - 1:
                    if previous != elem:
                        text += self.compression_rle(previous, counter)
                        text += str(elem)
                    else:
                        text += self.compression_rle(previous, counter + 1)
                else:
                    if elem != previous:
                        text += self.compression_rle(previous, counter)
                        previous = elem
                        counter = 1
                    else:
                        counter += 1
            print(text)


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./kinduction.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

    pn = PetriNet(sys.argv[1])
    
    if len(sys.argv) == 3:
        pn_reduced = PetriNet(sys.argv[2])
        eq = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())
    else:
        pn_reduced = None
        eq = None
    
    concurrent_places = ConcurrentPlaces(pn, pn_reduced, eq)
    concurrent_places.analyze(10)

    print("Result computed using z3")
    print("------------------------")
    concurrent_places.display(False)
    print("------------------------")
    concurrent_places.display(True)
