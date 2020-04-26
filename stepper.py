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
    def __init__(self, pn):
        """ Initializer.
        """
        self.pn = pn

        self.transitions = [*self.pn.transitions]

        # A precondition vector associated to each transition
        self.pre = {}
        # A delta vector assiciated to each transition
        self.delta = {}

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

    def get_markings(self, m=None, c=None):
        """
        """
        new_markings = []

        # Shuffle the transtitions
        shuffle(self.transitions)

        # Iterate over transitions until one is fireable
        for tr in self.transitions:
            if self.is_fireable(tr, m): # fireable
                if True: # new marking
                    break

        return new_markings

    def is_fireable(self, tr, marking):
        """ Check if a transitions is fireable given a marking.
        """
        pre = self.pre[tr]
        return True

if __name__ == '__main__':
    
    if len(sys.argv) == 1:
        exit("File missing: ./stepper <path_to_file>")
    
    pn = PetriNet(sys.argv[1])
    stepper = Stepper(pn)

    print("Stepper")
    print("-------")
    print(stepper)
