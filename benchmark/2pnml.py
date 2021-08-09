#!/usr/bin/env python3

"""
Convert a `.ndr` or `.net` Petri net to `.pnml`
and set `id` attributes to `name/text/` values.
"""

import argparse
import subprocess
import xml.etree.ElementTree as ET
from pathlib import Path


def translator(filename):
    """ Translator.
    """
    # Convert to `.pnml`
    output = subprocess.run(["ndrio", filename, '-pnml'], stdout=subprocess.PIPE).stdout.decode('utf-8')
    
    xmlns = "{http://www.pnml.org/version-2009/grammar/pnml}"
    ET.register_namespace('', "http://www.pnml.org/version-2009/grammar/pnml")

    # Parse `.pnml`
    tree = ET.ElementTree(ET.fromstring(output))
    root = tree.getroot()

    # Set place `id`s to `text/name`
    for place_node in root.iter(xmlns + 'place'):
        place_name = place_node.find(xmlns + 'name/' + xmlns + 'text')
        place_node.attrib['id'] = place_name.text
        
    # Set transition `id`s to `text/name`
    for transition_node in root.iter(xmlns + 'transition'):
        transition_name = transition_node.find(xmlns + 'name/' + xmlns + 'text')
        transition_node.attrib['id'] = transition_name.text

    # Get output filename
    filename = Path(filename)
    out_filename = filename.with_suffix('.pnml')
    
    # Write `.pnml`
    tree.write(out_filename,  encoding="utf-8", xml_declaration=True)


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='Convert `.ndr` or `.net` to `.pnml` (mcc compliant)')

    parser.add_argument('path_ptnet',
                        metavar='ptnet',
                        type=str,
                        help='path to Petri net (.ndr or .net)')

    results = parser.parse_args()
    translator(results.path_ptnet)


if __name__ == "__main__":
    main()
    print("DONE")
    exit(0)
    
    
