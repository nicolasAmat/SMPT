#!/usr/bin/env python3

"""
SMPT is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

SMPT is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with SMPT. If not, see <https://www.gnu.org/licenses/>.
"""

import argparse
import csv
import os
import shutil
import subprocess

import numpy as np

TIMEOUT = 100

def benchmark_model(path_inputs, model, path_oracles):
    """
    """
    dest = "data/{}/".format(model)
    path_model = "{}/{}/model.net".format(path_inputs, model)

    if os.path.exists(dest):
        shutil.rmtree(dest)
    os.makedirs(dest)

    smpt = subprocess.Popen(['smpt', '--auto-reduce', '--display-reduction-ratio', '--display-time', path_model], stdout=subprocess.PIPE, encoding='utf-8')
    smpt_output = smpt.stdout.readlines()
    reduction_data = smpt_output[0].rstrip().split(' ')
    
    if len(reduction_data) >= 3:
        reduction_ratio = int(reduction_data[1].replace('RR~', '').replace('%', ''))
        reduction_time = reduction_data[2].replace('t~', '').replace('s', '')
    else:
        reduction_ratio = np.nan
        reduction_time = np.nan

    analysis = reduction_ratio >= 30

    with open(dest + 'reduction.csv', 'w') as reduction_file:
        reduction_writer = csv.writer(reduction_file)
        reduction_writer.writerow(['net', 'time', 'ratio', 'analysis'])
        reduction_writer.writerow([model, reduction_time, reduction_ratio, analysis])

    

def benchmark_property(path_inputs, model, path_oracles, property):
    """
    """
    pass


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='Benchmark Script')

    parser.add_argument('path_inputs',
                        metavar='inputs',
                        type=str,
                        help='path to inputs directory')

    parser.add_argument('path_inputs_list',
                        metavar='inputs_list',
                        type=str,
                        help='path to inputs list')

    parser.add_argument('path_oracles',
                        metavar='oracles',
                        type=str,
                        help='path to oracles directory')

    parser.add_argument('--generate-common-file',
                        action='store_true',
                        help='path to oracles directory')

    results = parser.parse_args()

    # Create 'data/' directory
    if not os.path.exists('data'):
        os.makedirs('data')

    # Read inputs list
    try:
        with open(results.path_inputs_list, 'r') as fp_inputs_list:
            for model in fp_inputs_list.readlines():
                model = model.strip()
                print(model)
                benchmark_model(results.path_inputs, model, results.path_oracles)
        fp_inputs_list.close()
    except FileNotFoundError as e:
        exit(e)

if __name__ == "__main__":
    main()
    exit(0)
