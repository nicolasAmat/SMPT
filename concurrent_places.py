#!/usr/bin/env python3

"""
Concurrent Places Analyzer.

Ref: Garavel, “Nested-Unit Petri Nets.”
"""

from pn import PetriNet, Place
from eq import System, Relation
from formula import Formula, Clause, Inequality
from k_induction import KInduction

import sys
from threading import Thread, Event

stop_it_concurrent_places = Event()


class ConcurrentPlaces:
    """ 
    Concurrent Places Analyzer.
    """

    def __init__(self, pn, pn_reduced=None, eq=None, debug=False):
        """ Initializer.
        """
        self.pn = pn
        self.pn_reduced = pn_reduced
        self.eq = eq
        self.debug = debug

        self.matrix = None
        
        self.reduced = eq is not None
        
        if self.reduced:
            self.matrix_reduced = None
            self.pn_analyzed = self.pn_reduced
        else:
            self.pn_analyzed = self.pn

        self.formula = Formula(pn, prop='concurrent_places')
        self.c = []

    def analyze(self, timeout):
        """
        Run Concurrent Places Analysis using k-induction.
        """
        self.build_matrix()
        self.initialization()

        if self.pn_analyzed.places != {}:
            proc = Thread(target=self.iterate)
            proc.start()
            proc.join(timeout)
            stop_it_concurrent_places.set()

        if self.reduced:
            self.analyze_reduced()

    def analyze_reduced(self):
        """
        Analysis on a reduced net.
        """
        relation = Relation(self.eq)
        c_stables = relation.trivial_c_stables()
        
        for c_stable in c_stables:
            self.fill_matrix(self.place_translator(c_stable), self.matrix)

        for i, line in enumerate(self.matrix_reduced):
            for j, concurrent in enumerate(line):
                if i != j and concurrent:
                        var1 = self.pn_reduced.ordered_places[i]
                        var2 = self.pn_reduced.ordered_places[j]

                        if var1 not in self.pn.places.values() or var2 not in self.pn.places.values():
                            c_stables = relation.c_stable_matrix(var1, var2)
                            for c_stable in c_stables:
                                self.fill_matrix(self.place_translator(c_stable), self.matrix)

                        else:
                            pl1, pl2 = self.pn.places[var1.id], self.pn.places[var2.id]
                            self.fill_matrix([pl1, pl2], self.matrix)

    def build_matrix(self):
        """ Build a dictionary that create an order on the places.
            Assumption: No Dead Place
        """
        self.matrix = [[0 for j in range(i + 1)] for i in range(self.pn.counter_places)]
        for i in range(self.pn.counter_places):
            self.matrix[i][i] = 1
        self.matrix_analyzed = self.matrix

        if self.reduced:
            self.matrix_reduced = [[0 for j in range(i + 1)] for i in range(self.pn_reduced.counter_places)]
            for i in range(self.pn_reduced.counter_places):
                self.matrix_reduced[i][i] = 1
            self.matrix_analyzed = self.matrix_reduced

    def initialization(self):
        """ Initialization.
            If at least two places in m0 are marked,
            C := {m0}
        """
        m_zero = []

        for pl in self.pn_analyzed.places.values():
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

            k_induction = KInduction(self.pn_analyzed, self.formula, debug=self.debug)
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

        for pl in self.pn_analyzed.places.values():
            if pl not in m:
                inequalities.append(Inequality(pl, 0, '>'))
        cl = Clause(inequalities, 'or')
        self.formula.clauses.append(cl)

        self.fill_matrix(m, self.matrix_analyzed)

    def fill_matrix(self, c, matrix):
        """ Fill a c-stable c in the Concurrent Places matrix.
        """
        for index, pl1 in enumerate(c):
            for pl2 in c[index + 1:]:
                if pl1.order > pl2.order:
                    matrix[pl1.order][pl2.order] = 1 
                else:
                    matrix[pl2.order][pl1.order] = 1

    def place_translator(self, c):
        """ Take a c-stable c with ids of places,
            return same c-stable with places from the initial net.
        """
        return [self.pn.places[id_pl] for id_pl in c]

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

    def display_matrix(self):
        """ Display Concurrent Places matrix.
            Half matrix, raw format.
        """
        for index, line in enumerate(self.matrix):
            print(self.pn.ordered_places[index].id, ' '.join(map(str, line)))

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

    def compression_rle(self, elem, counter):
        """ Run-Length Encoding helper.
        """
        if counter < 4:
            return str(elem) * counter
        else:
            return "{}({})".format(elem, counter)


if __name__ == '__main__':
    
    if len(sys.argv) < 2:
        exit("File missing: ./concurrent_places.py <path_to_initial_petri_net> [<path_to_reduce_net>]")

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
