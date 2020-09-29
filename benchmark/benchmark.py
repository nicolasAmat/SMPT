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


TIMEOUT = '60'
MIN_REDUCTION_RATIO = 30


def benchmark_model(path_inputs, model, path_oracles):
    """ Bencharmark a model.
    """
    dest = "data/{}/".format(model)
    path_model = "{}/{}/model.net".format(path_inputs, model)

    # Clean 'dest' directory
    if os.path.exists(dest):
        shutil.rmtree(dest)
    os.makedirs(dest)

    # Run SMPT without any property
    smpt = subprocess.Popen(['smpt', '--auto-reduce', '--display-reduction-ratio', '--display-time', path_model], stdout=subprocess.PIPE, encoding='utf-8')
    smpt_output = smpt.stdout.readlines()
    smpt.stdout.close()
    reduction_data = smpt_output[0].rstrip().split(' ')
    
    # Get reduction information
    if len(reduction_data) >= 3:
        reduction_ratio = int(reduction_data[1].replace('RR~', '').replace('%', ''))
        reduction_time = reduction_data[2].replace('t~', '').replace('s', '')
    else:
        reduction_ratio = np.nan
        reduction_time = np.nan

    # Run property analysis if the reduction ratio is greater than the minimum defined
    analysis = reduction_ratio >= MIN_REDUCTION_RATIO

    # Write model information in `reduction.csv`
    with open(dest + 'reduction.csv', 'w') as reduction_file:
        reduction_writer = csv.writer(reduction_file)
        reduction_writer.writerow(['MODEL', 'TIME', 'RATIO', 'ANALYSIS'])
        
        # Write and print reduction data
        reduction_data = [model, reduction_time, reduction_ratio, analysis]
        reduction_writer.writerow(reduction_data)
        print(' '.join(map(str, reduction_data)))
    
    # Run analysis benchmarks
    if analysis:
        for properties in ['RC', 'RF', 'RD']:
            benchmark_properties(path_inputs, model, path_model, path_oracles, dest, properties)


def benchmark_properties(path_inputs, model, path_model, path_oracles, dest, properties):
    """ Benchmark properties on a model.
    """
    # Get the corresponding properties option
    if properties == 'RC':
        properties_option = ['--xml', "{}/{}/ReachabilityCardinality.xml".format(path_inputs, model)]
    if properties == 'RF':
        properties_option = ['--xml', "{}/{}/ReachabilityFireability.xml".format(path_inputs, model)]
    if properties == 'RD':
        properties_option = ['--deadlock']

    basic_options = ['smpt', '--display-method', '--display-time', '--timeout', TIMEOUT, path_model] + properties_option

    # Run SMPT with reduction
    smpt_with_reduction = subprocess.Popen(basic_options + ['--auto-reduce'], stdout=subprocess.PIPE, encoding='utf-8')
    smpt_output_with_reduction = smpt_with_reduction.stdout.readlines()
    smpt_with_reduction.stdout.close()
    
    # Run SMPT without reduction
    smpt_without_reduction = subprocess.Popen(basic_options, stdout=subprocess.PIPE, encoding='utf-8')
    smpt_output_without_reduction = smpt_without_reduction.stdout.readlines()
    smpt_without_reduction.stdout.close()
    
    # Read oracles
    try:
        with open('{}/{}-{}.out'.format(path_oracles, model, properties)) as fp_oracles:
            oracles = fp_oracles.readlines()
        fp_oracles.close()
    except FileNotFoundError as e:
        exit(e)

    with open("{}/{}.csv".format(dest, properties), 'w') as result_file:

        result_writer = csv.writer(result_file)
        result_writer.writerow(['MODEL', 'PROPERTY', 'MONOTONE', 'TIME_WITH_REDUCTION', 'METHOD_WITH_REDUCTION', 'CORRECTNESS_WITH_REDUCTION', 'TIME_WITHOUT_REDUCTION', 'METHOD_WITHOUT_REDUCTION', 'CORRECTNESS_WITHOUT_REDUCTION'])

        for prop_with_reduction, prop_without_reduction, prop_oracle in zip(smpt_output_with_reduction[1:], smpt_output_without_reduction[1:], oracles[1:]):
            prop_with_reduction, prop_without_reduction, prop_oracle = prop_with_reduction.strip().split(' '), prop_without_reduction.strip().split(' '), prop_oracle.strip().split(' ')
            
            # Assert property ids are equal
            assert(prop_with_reduction[0] == prop_oracle[1])
            assert(prop_without_reduction[0] == prop_oracle[1])

            # Get property data
            property_data = [model, prop_oracle[1], prop_with_reduction[-1] == '(IC3_auto-disabled)']

            # Get analysis with reduction dat
            if prop_with_reduction[1] == 'TIMEOUT':
                analysis_with_reduction_data = [np.nan, 'None', 'None']
            else:
                analysis_with_reduction_data = [prop_with_reduction[2], prop_with_reduction[3], prop_with_reduction[1] == prop_oracle[2]]

            # Get analysis without reduction data
            if prop_without_reduction[1] == 'TIMEOUT':
                analysis_without_reduction_data = [np.nan, 'None', 'None']
            else:
                analysis_without_reduction_data = [prop_without_reduction[2], prop_without_reduction[3], prop_without_reduction[1] == prop_oracle[2]]

            # Get full data
            property_data += analysis_with_reduction_data + analysis_without_reduction_data

            # Write and print property data
            result_writer.writerow(property_data)
            print(' '.join(map(str, property_data)))


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='SMPT Benchmark Script')

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

    parser.add_argument('--merge_files',
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
