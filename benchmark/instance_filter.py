#!/usr/bin/env python3

"""
Filter instances with a minimum and maximum reduction ratio.
"""

import argparse
import os

import numpy as np
import pandas as pd


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='Filter instances with a minimum reduction ratio')

    parser.add_argument('path_reductions_csv',
                        metavar='csv',
                        type=str,
                        help='path to reductions csv')

    parser.add_argument('path_instances_list',
                        metavar='list',
                        type=str,
                        help='path to instances list')

    parser.add_argument('path_filtered_list',
                        metavar='filtered_list',
                        type=str,
                        help='path to filtered instances list')

    parser.add_argument('min',
                        metavar='min',
                        type=float,
                        help='minimum reduction ratio')

    parser.add_argument('max',
                        metavar='max',
                        type=float,
                        help='maximum reduction ratio')

    results = parser.parse_args()

    # Read data frame
    df_reductions = pd.read_csv(results.path_reductions_csv)

    # Read instances list
    with open(results.path_instances_list, 'r') as fp_reductions:
        instances = fp_reductions.read().splitlines()

    # Write the filtered instances list
    with open(results.path_filtered_list, 'w') as fp_filtered:

        for instance in instances:
            # Get the instance name
            instance_name = os.path.basename(instance).replace('.pnml', '')
            # Get the corresponding reduction ratio
            ratio = df_reductions.query('INSTANCE == "{}"'.format(instance_name))['RATIO'].values
            # Write the instance in the output list if the reduction ratio is greater than the minimum one
            if ratio and ratio[0] >= results.min and ratio[0] <= results.max:
                fp_filtered.write(instance + '\n')
                print(instance_name)


if __name__ == "__main__":
    main()
    print("DONE")
    exit(0)
