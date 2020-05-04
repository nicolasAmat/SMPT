#!/usr/bin/env python3

"""
Petri Net Stepper.
"""

from pn import PetriNet

import sys


class Stepper:
    """
    Stepper.
    """
    def __init__(self, pn, concurrent_places=None):
        """ Initializer.
        """
        self.pn = pn

        # A precondition vector associated to each transition
        self.pre = {}
        # A delta vector assiciated to each transition
        self.delta = {}

        # List of markings (list of marked places) already explored
        self.c = []

        self.initialization()

    def __str__(self):
        """ Stepper to String.
            Output: `pre` and `delta` vectors associated to each transitions.
        """
        text = ""
        for tr in self.pn.transitions:
            text += tr + ":"
            pre, delta = self.pre[tr], self.delta[tr]
            
            text +=  "\n\t> Pre: "
            for order, weight in enumerate(pre):
                pl_id = self.pn.ordered_places[order].id
                if weight > 0:
                    text += " " + pl_id + " > " + str(weight)
                if weight < 0:
                    text += " " + pl_id + " < " + str(-weight)

            text +=  "\n\t> Delta: "
            for order, weight in enumerate(delta):
                pl_id = self.pn.ordered_places[order].id
                if weight > 0:
                    text += " " + pl_id + "' = " + pl_id + " + " + str(weight) 
                if weight < 0:
                    text += " " + pl_id + "' = " + pl_id + " - " + str(-weight)
            text += "\n"

        return text
    
    def initialization(self):
        """ Initialize `pre` and `delta` vetors for each transition.
        """
        for tr_id, tr in self.pn.transitions.items():
            
            pre = [0 for _ in range(self.pn.counter_places)]
            delta = [0 for _ in range(self.pn.counter_places)]
            
            for pl, weight in tr.input.items():
                pre[pl.order] = weight
                if weight > 0:
                    delta[pl.order] = - weight

            for pl, weight in tr.output.items():
                delta[pl.order] += weight

            self.pre[tr_id], self.delta[tr_id] = pre, delta

    def get_markings(self, marking_vector):
        """ Return a list of new markings not included in `c`
            reachable in one step.
        """
        new_markings = []

        # Iterate over transitions until one is fireable
        for tr in self.pn.transitions:
        
            # Check if tr is fireable
            if self.is_fireable(tr, marking_vector):
                
                # Compute the resulting marking
                new_marking = [m + delta for m, delta in zip(marking_vector, self.delta[tr])]
                new_marked_places = [self.pn.ordered_places[index] for index, marking in enumerate(new_marking) if marking > 0]

                # Check if the new marking is not included in markings already explored
                if self.not_explored(new_marked_places):
                    new_markings.append(new_marking)
                    self.add_clique(new_marked_places)
        
        return new_markings

    def is_fireable(self, tr, marking):
        """ Check if a transitions is fireable given a marking.
        """
        for pl_cond, pl_m in zip(self.pre[tr], marking):
            
            # Normal Arc
            if pl_cond > 0 and pl_m < pl_cond:
                return False

            # Inhibitor Arc
            if pl_cond < 0 and pl_m >= pl_cond:
                return False
            
        return True

    def not_explored(self, new_marked_places):
        """ Check if the new marking contains at least two marked palces,
            and if it is not included in markings already explored (`c`).
        """
        if len(new_marked_places) < 2:
            return False

        for marked_places in self.c:
            if set(new_marked_places) <= set(marked_places):
                return False

        return True

    def add_clique(self, clique):
        """ Add a clique to `c`.
            Include cliques maximization.
        """
        # Restore old value
        for pl in self.pn.places.values():
            pl.card_concurrency_relation_old = pl.card_concurrency_relation
        
        # Update new value
        for pl in clique:
            pl.card_concurrency_relation += len(clique) - 1

        for cl in self.c[:]:
            if all(pl.card_concurrency_relation != pl.card_concurrency_relation_old for pl in cl):
                self.c.remove(cl)

        self.c.append(clique)


if __name__ == '__main__':
    
    if len(sys.argv) == 1:
        exit("File missing: ./stepper <path_to_net>")
    
    pn = PetriNet(sys.argv[1])
    
    c = [[pl for pl in pn.places.values() if pl.marking > 0]]

    stepper = Stepper(pn, c)

    print("Stepper")
    print("-------")
    print(stepper)

    print("Marking Vectors")
    print("--------")
    
    marking_vector = [pl.marking for pl in pn.ordered_places]
    print("---Initial Markings---")
    print(marking_vector)
    
    print("---One-step Markings---")
    markings_1 = stepper.get_markings(marking_vector)
    for marking in markings_1:
        print(marking)

    print("---Two-steps Markings---")
    markings_2 = []
    for marking in markings_1:
        markings_2 += stepper.get_markings(marking)
    for marking in markings_2:
        print(marking)
