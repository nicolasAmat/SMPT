#!/usr/bin/env python3

"""
Petri Net Stepper.
"""

from pn import PetriNet

from random import shuffle
import sys


class Stepper:
    """
    Stepper.
    """
    def __init__(self, pn, c=[]):
        """ Initializer.
        """
        self.pn = pn

        self.transitions = [*self.pn.transitions]

        # A precondition vector associated to each transition
        self.pre = {}
        # A delta vector assiciated to each transition
        self.delta = {}

        self.c = c

        self.initialization()

    def __str__(self):
        """ Stepper to String.
            Output: `pre` and `delta` vectors associated to each transitions.
        """
        text = ""
        for tr in self.transitions:
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
        """ Initialize `pre` and `delta` vetors.
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

        # Shuffle the transtitions
        shuffle(self.transitions)

        # Iterate over transitions until one is fireable
        for tr in self.transitions:
        
            # Check if tr is fireable
            if self.is_fireable(tr, marking_vector):
                
                # Compute the resulting marking
                new_marking = [m + delta for m, delta in zip(marking_vector, self.delta[tr])]
                marked_place = [self.pn.ordered_places[index] for index, marking in enumerate(new_marking) if marking > 0]

                # Check if the new marking is not included in markings already explored
                if self.contains_new_pair(marked_place):
                    new_markings.append(new_marking)
                    self.c.append(new_marking)
        
        return new_markings

    def is_fireable(self, tr, m):
        """ Check if a transitions is fireable given a marking.
        """
        for pl_cond, pl_m in zip(self.pre[tr], m):
            
            # Normal Arc
            if pl_cond > 0 and pl_m < pl_cond:
                return False

            # Inhibitor Arc
            if pl_cond < 0 and pl_m >= pl_cond:
                return False
            
        return True

    def contains_new_pair(self, new_m):
        """ Check if a new marking is not a included in a list of markings.
        """
        for m in self.c:

            if set(new_m) <= set(m):
                return False

        return True

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

