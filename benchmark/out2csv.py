#!/usr/bin/env python3

"""
OUT 2 CSV Script for SMPT Benchmarking.
"""

import argparse
import csv
import glob
import os
import shutil

import numpy as np
import pandas as pd


def out_2_csv(path_outputs, path_oracles):
    """ Convert .out files to .csv files.
    """
    # Get instances names
    instances = [instance for instance in os.listdir(path_outputs)]
    
    for instance in instances:
        # Check if there is a `reduction.out` file
        if os.path.isfile('{}/{}/reduction.out'.format(path_outputs, instance)):
            reduction_converter(path_outputs, instance)
        
        # Check if there is a `{RC,RF,RD}_with_reduction.out` file
        if os.path.isfile('{}/{}/RC_with_reduction.out'.format(path_outputs, instance)) or os.path.isfile('{}/{}/RF_with_reduction.out'.format(path_outputs, instance)) or os.path.isfile('{}/{}/RD_with_reduction.out'.format(path_outputs, instance)):
            for properties in ['RC', 'RD', 'RF']:
                properties_converter(path_outputs, instance, properties, path_oracles)

def reduction_converter(path_outputs, instance):
    """ Convert  `reduction.out` to `reduction.csv`.
    """
    # Open `reduction.out`
    with open('{}/{}/reduction.out'.format(path_outputs, instance)) as out_reduction:
        reduction_data = out_reduction.readlines()[0].rstrip().split(' ')

    # Get reduction data
    if len(reduction_data) >= 3:
        reduction_ratio = int(reduction_data[1].replace('RR~', '').replace('%', ''))
        reduction_time = reduction_data[2].replace('t~', '').replace('s', '')
    else:
        reduction_ratio = np.nan
        reduction_time = np.nan

    # Write reduction data in `reduction.csv`
    with open('{}/{}/reduction.csv'.format(path_outputs, instance), 'w') as csv_reduction:
        reduction_writer = csv.writer(csv_reduction)
        reduction_writer.writerow(['INSTANCE', 'TIME', 'RATIO'])
        
        reduction_data = [instance, reduction_time, reduction_ratio]
        reduction_writer.writerow(reduction_data)
        print(' '.join(map(str, reduction_data)))

def properties_converter(path_outputs, instance, properties, path_oracles):
    """ Convert `{RC,RF,RD}_with_reduction.csv` and `{RC,RF,RD}_without_reduction.out` to `{RC,RF,RD}.csv`.
    """
    # Check is the file exists with and without reduction
    if not (os.path.isfile('{}/{}/{}_with_reduction.out'.format(path_outputs, instance, properties)) and os.path.isfile('{}/{}/{}_without_reduction.out'.format(path_outputs, instance, properties))):
        return

    # Read oracles, if they do not exist do nothing
    try:
        with open('{}/{}-{}.out'.format(path_oracles, instance, properties)) as fp_oracles:
            oracles = fp_oracles.readlines()
        fp_oracles.close()
    except FileNotFoundError as e:
        return

    # Open `{properties}_with_reduction.out`
    with open('{}/{}/{}_with_reduction.out'.format(path_outputs, instance, properties)) as out_with_reduction:
        properties_with_reduction = out_with_reduction.readlines()
    
    # Open `{properties}_with_reduction.out`
    with open('{}/{}/{}_without_reduction.out'.format(path_outputs, instance, properties)) as out_without_reduction:
        properties_without_reduction = out_without_reduction.readlines()

    # Write properties information to `{RC,RF,RD}.csv`
    with open("{}/{}/{}.csv".format(path_outputs, instance, properties), 'w') as result_file:

        result_writer = csv.writer(result_file)
        result_writer.writerow(['INSTANCE', 'PROPERTY', 'MONOTONIC', 'TIME_WITH_REDUCTION', 'METHOD_WITH_REDUCTION', 'CORRECTNESS_WITH_REDUCTION', 'TIME_WITHOUT_REDUCTION', 'METHOD_WITHOUT_REDUCTION', 'CORRECTNESS_WITHOUT_REDUCTION'])

        for prop_with_reduction, prop_without_reduction, prop_oracle in zip(properties_with_reduction[1:], properties_without_reduction[1:], oracles[1:]):
            prop_with_reduction, prop_without_reduction, prop_oracle = prop_with_reduction.strip().split(' '), prop_without_reduction.strip().split(' '), prop_oracle.strip().split(' ')

            # Get property data
            property_data = [instance, prop_oracle[1], prop_with_reduction[1] != 'SKIPPED' and prop_with_reduction[-1] != '(IC3_auto-disabled)']

            # Get analysis with reduction dat
            if prop_with_reduction[1] == 'SKIPPED':
                analysis_with_reduction_data = [np.nan, 'None', 'Skipped']
            elif prop_with_reduction[1] == 'TIMEOUT':
                analysis_with_reduction_data = [np.nan, 'None', 'None']
            else:
                analysis_with_reduction_data = [prop_with_reduction[2], prop_with_reduction[3], prop_with_reduction[1] == prop_oracle[2]]

            # Get analysis without reduction data
            if prop_without_reduction[1] == 'SKIPPED':
                analysis_without_reduction_data = [np.nan, 'None', 'Skipped']
            elif prop_without_reduction[1] == 'TIMEOUT':
                analysis_without_reduction_data = [np.nan, 'None', 'None']
            else:
                analysis_without_reduction_data = [prop_without_reduction[2], prop_without_reduction[3], prop_without_reduction[1] == prop_oracle[2]]

            # Get full data
            property_data += analysis_with_reduction_data + analysis_without_reduction_data

            # Write and print property data
            result_writer.writerow(property_data)
            print(' '.join(map(str, property_data)))

def merge_files(path_outputs):
    """ Merge .csv file in common files.
    """
    merged_path = '{}/merged/'.format(path_outputs)

    # Delete `merged` directory
    if os.path.exists(merged_path):
        shutil.rmtree(merged_path)
    
    # Create `merged` folder
    os.makedirs(merged_path)
    
    # Merge files
    for csv_filename in ['reduction.csv', 'RC.csv', 'RF.csv', 'RD.csv']:
        print(csv_filename)
        csv_filenames = [filename for filename in glob.iglob('{}/**/*{}'.format(path_outputs, csv_filename), recursive=True)]
        if csv_filenames:
            merged_csv = pd.concat([pd.read_csv(filename) for filename in csv_filenames])
            merged_csv.to_csv(merged_path + csv_filename, index=False, encoding='utf-8')

def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='SMPT Benchmark Script')

    parser.add_argument('path_outputs',
                        metavar='outputs',
                        type=str,
                        help='path to outputs directory')

    parser.add_argument('path_oracles',
                        metavar='oracles',
                        type=str,
                        help='path to oracles directory')

    parser.add_argument('--merge-files',
                        action='store_true',
                        help='path to oracles directory')

    results = parser.parse_args()

    out_2_csv(results.path_outputs, results.path_oracles)

    # Merge files
    if results.merge_files:
        merge_files(results.path_outputs)


if __name__ == "__main__":
    main()
    print("DONE")
    exit(0)
