#!/usr/bin/env python3

"""
Translate an initial marking from a .pnml Petri net to an .xml formula.
"""

import argparse
import xml.etree.ElementTree as ET


def translator(filename, mcc=True):
    """ Marking translator.
        Option mcc: Model Checking Contest compliant.
    """
    xmlns = "{http://www.pnml.org/version-2009/grammar/pnml}"

    tree = ET.parse(filename)
    root = tree.getroot()

    property_set = ET.Element('property-set')
    property = ET.SubElement(property_set, 'property')
    id = ET.SubElement(property, 'id')
    id.text = "Marking"
    description = ET.SubElement(property, 'description')
    description.text = "Automatically generated"
    formula = ET.SubElement(property, 'formula')
    formula = ET.SubElement(formula, 'exists-path')
    formula = ET.SubElement(formula, 'finally')
    formula = ET.SubElement(formula, 'conjunction')

    for place_node in root.iter(xmlns + "place"):
        pl = place_node.find(xmlns + "name/" + xmlns + "text").text
        initial_marking = place_node.find(xmlns + "initialMarking/" + xmlns + "text")
        
        if initial_marking is not None:

            if mcc:
                integer_le = ET.SubElement(formula, "integer-le")
                token_count = ET.SubElement(integer_le, "tokens-count")
                place = ET.SubElement(token_count, 'place')
                place.text = pl
                integer_constant = ET.SubElement(integer_le, "integer-constant")
                integer_constant.text = initial_marking.text

                negation =  ET.SubElement(formula, "negation")
                integer_le = ET.SubElement(negation, "integer-le")
                token_count = ET.SubElement(integer_le, "tokens-count")
                place = ET.SubElement(token_count, 'place')
                place.text = pl
                integer_constant = ET.SubElement(integer_le, "integer-constant")
                integer_constant.text = str(int(initial_marking.text) - 1)
            
            else:
                integer_le = ET.SubElement(formula, "integer-eq")
                token_count = ET.SubElement(integer_le, "tokens-count")
                place = ET.SubElement(token_count, 'place')
                place.text = pl
                integer_constant = ET.SubElement(integer_le, "integer-constant")
                integer_constant.text = initial_marking.text

    indent(property_set)
    ET.ElementTree(property_set).write(filename.replace('.pnml', '.xml'),  encoding="utf-8", xml_declaration=True)


def indent(elem, level=0):
    """ Indent .xml.
    """
    i = "\n" + level*"  "
    if len(elem):
        if not elem.text or not elem.text.strip():
            elem.text = i + "  "
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
        for elem in elem:
            indent(elem, level+1)
        if not elem.tail or not elem.tail.strip():
            elem.tail = i
    else:
        if level and (not elem.tail or not elem.tail.strip()):
            elem.tail = i


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='Transform an inital marking into a reachability formula')

    parser.add_argument('path_pnml',
                        metavar='pnml',
                        type=str,
                        help='path to the .pnml Petri net')

    parser.add_argument('--mcc',
                        action='store_true',
                        help='MCC compliant formula')

    results = parser.parse_args()
    translator(results.path_pnml, results.mcc)


if __name__ == "__main__":
    main()
    print("DONE")
    exit(0)
    
    
