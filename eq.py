#!/usr/bin/env python3

"""
Reduction Equations Module

Equations provided by the tool `reduce`
Input file format: .net
"""
from pn import PetriNet

import re
import sys


class System:
    """
    Equation system defined by:
    - a set of places from the original Petri Net
    - a set of places from the reduced Petri Net
    - a set of additional variables
    - a set of (in)equations
    """
    def __init__(self, filename, places = [], places_reduced = []):
        self.places = places
        self.places_reduced = places_reduced
        self.additional_vars = []

        self.system = []

        self.parser(filename)

    def __str__(self):
        """ Equations to `reduce` tool format
        """
        text = ""
        for eq in self.system:
            text += str(eq) + '\n'
        return text

    def smtlib(self):
        """ Equations,
            Declarations of the additional variables.
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var, var)
        for eq in self.system:
            smt_input += eq.smtlib() + '\n'
        return smt_input

    def smtlib_only_non_reduced_places(self, k_original=None):
        """ Equations not involving places in the reduced net,
            Declarations of the additional variables,
            k_original: used by IC3.
            SMT-LIB format
        """
        smt_input = ""
        for var in self.additional_vars:
            if var not in self.places_reduced:
                var_name = var if k_original is None else "{}@{}".format(var, k_original) 
                smt_input += "(declare-const {} Int)\n(assert (>= {} 0))\n".format(var_name, var_name)
        for eq in self.system:
            if not eq.contain_reduced:
                smt_input += eq.smtlib(k_original, [*self.places] + self.additional_vars) + '\n'
        return smt_input
        
    def smtlib_ordered(self, k, k_original=None):
        """ Equations involving places in the reduced net,
            k:          used by k-induction and IC3,
            k_original: used by IC3.
            SMR-LIB format
        """
        smt_input = ""
        for eq in self.system:
            if eq.contain_reduced:
                smt_input += eq.smtlib_ordered(k, k_original, self.places_reduced, [*self.places] + self.additional_vars) + '\n'
        for pl in self.places_reduced:
            if pl in self.places:
                if k_original is None:
                    smt_input += "(assert (= {}@{} {}))\n".format(pl, k, pl)
                else:
                    smt_input += "(assert (= {}@{} {}@{}))\n".format(pl, k, pl, k_original)
        return smt_input

    def parser(self, filename):
        """ System of reduction equations parser.
            Input format: .net (output of the `reduce` tool)
        """
        try:
            with open(filename, 'r') as fp:
                content = re.search(r'# generated equations\n(.*)?\n\n', fp.read(), re.DOTALL) 
                if content:
                    lines = re.split('\n+', content.group())[1:-1]
                    equations = [re.split(r'\s+', line.partition(' |- ')[2]) for line in lines]
                    for eq in equations:
                        self.system.append(Equation(eq, self))
            fp.close()
        except FileNotFoundError as e:
            exit(e)


class Equation:
    """
    Equation defined by:
    - Left member
    - Right member
    - Operator
    """
    def __init__(self, eq, system):
        self.left = []
        self.right = []
        self.operator = ""
        self.contain_reduced = False
        self.parse_equation(eq, system)

    def __str__(self):
        """ Equation to .net format.
        """
        return self.member_str(self.left) + '= ' + self.member_str(self.right)

    def member_str(self, member):
        """ Member to .net format.
        """
        text = ""
        for index, elem in enumerate(member):
            text += elem + " "
            if index != len(member) - 1:
                text += '+ '
        return text

    def smtlib(self, k_original=None, other_vars=[]):
        """ Equation.
            SMT-LIB format
        """
        return "(assert ({}".format(self.operator)                      \
               + self.member_smtlib(self.left, k_original, other_vars)  \
               + self.member_smtlib(self.right, k_original, other_vars) \
               + "))"

    def member_smtlib(self, member, k_original, other_vars):
        """ Member.
            SMT-LIB format
        """
        smt_input = ""
        if len(member) > 1:
            smt_input += " (+"
        for elem in member:
            if k_original is None or elem not in other_vars:
                smt_input += " {}".format(elem)
            else:
                smt_input += " {}@{}".format(elem, k_original)
        if len(member) > 1:
            smt_input += ")"
        return smt_input

    def smtlib_ordered(self, k, k_original, places_reduced, other_vars=[]):
        """ Equation with orders.
            k:              used by k-induction and IC3
            k_original:     used by IC3
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and original net
            SMTLIB format
        """
        return "(assert ({}".format(self.operator)                                                 \
               + self.member_smtlib_ordered(self.left, k, k_original, places_reduced, other_vars)  \
               + self.member_smtlib_ordered(self.right, k, k_original, places_reduced, other_vars) \
               + "))"

    def member_smtlib_ordered(self, member, k, k_original, places_reduced=[], other_vars = []):
        """ Equation with orders.
            k:              used by k-induction and IC3
            k_original:     used by IC3
            places_reduced: place identifiers from the reduced net
            other_vars:     other identifiers from equations and original net
            SMTLIB format
        """
        smt_input = ""
        if len(member) > 1:
            smt_input += " (+"
        for elem in member:
            if elem in places_reduced:
                smt_input += " {}@{}".format(elem, k)
            elif k_original is not None and elem in other_vars:
                smt_input += " {}@{}".format(elem, k_original)
            else:
                smt_input += " {}".format(elem)
        if len(member) > 1:
            smt_input += ")"
        return smt_input

    def parse_equation(self, eq, system):
        """ Equation parser.
            Input format: .net (output of the `reduced` tool)
        """
        left = True
        for element in eq:
            if element != '+':
                if element in ['=', '<=', '>=', '<', '>']:
                    self.operator = element
                    left = False
                else:
                    element = element.replace('{', '').replace('}', '').replace('#', '')
                    if not element.isnumeric():
                        if element not in system.places and element not in system.additional_vars:
                            system.additional_vars.append(element)
                        if element in system.places_reduced:
                            self.contain_reduced = True
                    if left:
                        self.left.append(element)
                    else:
                        self.right.append(element)


class Relation:
    """
    Graph relation between original net and reduced net.
    A relation is composed of:
    - Chains of agglomerations
    - Constant places
    - Equalities between places
    """
    def __init__(self, eq):
        self.eq = eq

        self.variables = {}

        self.agglomerations = []
        self.constant_places = []
        self.equal_places = []

        self.construct()
        self.propagate()

    def __str__(self):
        text = "Agglomerations\n--------------\n"
        for agglo in self.agglomerations:
            text += str(agglo) + '\n'
        text += "\nConstant Places\n---------------\n"
        for pl in self.constant_places:
            text += pl.id + ' = ' + str(pl.value) + '\n'
        text += "\nEqual Places\n------------\n"
        for eq in self.equal_places:
            text += eq[0].id + ' = ' + eq[1].id + '\n'
        
        return text

    def construct(self):
        """ Parse the equation and construct the relation.
        """
        for eq in self.eq.system:
            left = self.get_variable(eq.left[0])

            if len(eq.right) == 1:

                # case p = k
                if eq.right[0].isnumeric():
                    left.value = int(eq.right[0])
                    self.constant_places.append(left)

                # case p = q
                else:
                    right = self.get_variable(eq.right[0])
                    left.equals.append(right)
                    right.equals.append(left)
                    self.equal_places.append([left, right])
                
            else:
                
                right_1 = self.get_variable(eq.right[0])
                right_2 = self.get_variable(eq.right[1])

                # case p = q + r
                if not left.additional:
                    left.chidren = [right_1, right_2]
                
                else:
                
                    # case a = p + a'
                    if right_1.additional or right_2.additional:
                        left.children = [right_1, right_2]
                        if right_1 in self.agglomerations:
                            self.agglomerations.remove(right_1)
                        if right_2 in self.agglomerations:
                            self.agglomerations.remove(right_2)
                        self.agglomerations.append(left)

                    # case a = p + q
                    else:
                        left.children = [right_1, right_2]
                        self.agglomerations.append(left)

    def propagate(self):
        """ Propagate places to the head of each agglomeration.
            Propagate value of each agglomeration.
        """
        for var in self.agglomerations:
        
            places_propagated = []
            current_place = var
            value = var.value

            while True:
                
                if not current_place.additional:
                    places_propagated.append(current_place)

                for pl in current_place.equals:
                    if value > pl.value:
                        pl.value = value
                        self.constant_places.append(pl)

                left_child = current_place.children[0]
                right_child = current_place.children[1]

                if left_child.value < value:
                    left_child.value = value
                if right_child.value < value:
                    right_child.value = value

                if left_child.additional: 
                    places_propagated.append(right_child)
                    current_place = left_child
                elif right_child.additional:
                    places_propagated.append(left_child)
                    current_place = right_child
                else:
                    places_propagated.append(left_child)
                    places_propagated.append(right_child)
                    break

            var.places_propagated = places_propagated

        for var in self.constant_places:
            if not var.additional:
                var.places_propagated.append(var)


    def get_variable(self, id_var):
        """ Create the corresponding Variable
            if it is not already created,
            otherwise return the corresponding Variable.
        """
        if id_var in self.variables:
            return self.variables[id_var]
        else:
            new_var = Variable(id_var, id_var not in self.eq.places)
            self.variables[id_var] = new_var
            return new_var

    def trivial_c_stables(self):
        c_stables = []
        
        # agglomerations with a value > 1
        for var in self.agglomerations:
            # a_n = k > 1
            # a_n = p_n + a_n-1
            # ...
            # a_1 = p_1 + p_0
            if var.value > 1:
                c_stable = []
                for pl in var.places_propagated:
                    c_stable.append(pl.id)
                    for pl_eq in pl.equals:
                        c_stable.append(pl_eq.id)
                c_stables.append(c_stable)
            
            # p = q + r
            if not var.additional:
                c_stables.append([var, var.children[0]])
                c_stables.append([var, var.children[1]])

        # constant places and agglomerations
        if len(self.constant_places) > 0:
            for index, var1 in enumerate(self.constant_places):
                for var2 in self.constant_places[index + 1:]:
                    for pl1 in var1.places_propagated:
                        for pl2 in var2.places_propagated:
                            c_stables.append([pl1.id, pl2.id])
                            for pl_eq in pl1.equals:
                                c_stables.append([pl_eq.id, pl2.id])
                            for pl_eq in pl2.equals:
                                c_stables.append([pl1.id, pl_eq.id])
        
        # equals places
        for (var1, var2) in self.equal_places:
            if not (var1.additional or var2.additional):
                c_stables.append([var1.id, var2.id])
            
            else:
                for pl1 in var1.places_propagated:
                    for pl2 in var2.places_propagated:
                        c_stables.append([pl1.id, pl2.id])

        return c_stables

    def c_stable_matrix(self, var1, var2):
        var1 = self.get_variable(var1.id)
        var2 = self.get_variable(var2.id)
        
        c_stables = []

        for pl1 in var1.places_propagated:
            for pl2 in var2.places_propagated:
                c_stables.append([pl1.id, pl2.id])
                for pl_eq in pl1.equals:
                    if not pl_eq.additional:
                        c_stables.append([pl_eq.id, pl2.id])
                for pl_eq in pl2.equals:
                    if not pl_eq.additional:
                        c_stables.append([pl1.id, pl_eq.id])
        
        return c_stables

    def equalities(self):
        equals = []
        for var1, var2 in self.equal_places:
            if not (var1.additional or var2.additional):
                 equals.append([var1.id, var2.id])
        return equals


class Variable:
    """
    Place or additional variable.
    Used by the Concurrency Matrix Constructor.
    A variable defined by:
    - an ID
    - a value
    - a set of equals variables
    - a set of children
    """
    def __init__(self, id, additional):    
        self.id = id
        self.additional = additional

        self.value = -1
        self.equals = []
        self.children = None

        self.places_propagated = []

    def __str__(self):
        text = self.id + ':'
        for var in self.places_propagated:
            text += ' ' + var.id
        return text


if __name__ == "__main__":
    
    if len(sys.argv) < 3:
        exit("File missing: ./eq <path_to_initial_net> <path_to_reduced_net>")
    
    pn = PetriNet(sys.argv[1])
    pn_reduced = PetriNet(sys.argv[2])

    eq = System(sys.argv[2], pn.places.keys(), pn_reduced.places.keys())

    relation = Relation(eq)

    print("Equations")
    print("---------")
    print(eq)
    
    print("\nSMTlib2 Format")
    print("--------------")
    print(eq.smtlib())

    print("\nRelations")
    print("---------")
    print(relation)

