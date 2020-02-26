#!/usr/bin/env python3

class PetriNet:
    """
    Petri Net
    """
    def __init__(self, id):
        self.id = id
        self.places = {}
        self.transitions = {}

    def __str__(self):
        result = "net {}\n".format(self.id)
        for pl in self.places.values():
            result += str(pl)
        for tr in self.transitions.values():
            result += str(tr)
        return result

class Place:
    """
    Place
    """
    def __init__(self, id, marking = 0):
        self.id = id
        self.marking = marking

    def __str__(self):
        text = ""
        if self.marking != 0:
            text = "pl {} ({})\n".format(self.id, self.marking)
        return text

class Transition:
    """
    Transition
    """
    def __init__(self, id):
        self.id = id
        self.src = []
        self.dest = []

    def __str__(self):
        text = "tr {}  ".format(self.id)
        for src in self.src:
            text += src.id + " "
        text += '-> '
        for dest in self.dest:
            text += dest.id + " "
        text += '\n'
        return text

class NetParser:
    """
    Petri Net Parser
    Input: .net file format
    """
    def __init__(self, filename):
        self.net = None
        self.parseNet(filename)
        print(self.net)

    def parseNet(self, filename):
        try:
            with open(filename, 'r') as fp:
                for line in fp.readlines():
                    content = line.strip().split(' ')
                    element = content.pop(0)
                    if element == "net":
                        self.net = PetriNet(content[0])
                    if element == "tr":
                        self.parseTransition(content)
                    if element == "pl":
                        self.parsePlace(content)
        except FileNotFoundError as e:
            exit(e)

    def parseTransition(self, content):
        tr = Transition(content.pop(0))
        
        arrow = content.index("->")
        src = content[1:arrow]
        dst = content[arrow + 1:]

        for pl in src:
            if pl not in self.net.places:
                self.net.places[pl] = Place(pl)
            tr.src.append(self.net.places.get(pl))

        for pl in dst:
            if pl not in self.net.places:
                self.net.places[pl] = Place(pl)
            tr.dest.append(self.net.places.get(pl))

        self.net.transitions[tr.id] = tr


    def parsePlace(self, content):
        placeId = content.pop(0)
        if placeId not in self.net.places:
            self.net.places[placeId] = Place(placeId)
        self.net.places.get(placeId).marking = content[0].replace('(', '').replace(')', '')

if __name__ == "__main__":
    parser = NetParser("../nets_examples/airplane.net")