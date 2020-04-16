#!/usr/bin/env python3

"""
Petri Net Stepper.
"""

class Stepper:
    """
    Stepper.
    """
    def __init__(self, pn):
        """ Initializer.
        """
        self.pn = pn
        # A precondition vector associated to each transition
        self.pre = {}
        # A delta vector assiciated to each transition
        self.delta = {}

    def initialization(self):
        for tr in self.pn.transitions.values():
            pass

    
if __name__ == '__main__':
    pass

