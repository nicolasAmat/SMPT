#!/usr/bin/env python3

#!/usr/bin/env python3

"""
.out to .csv script.
"""

import argparse
import csv
import os


def main():
    """ Main function.
    """
    # Arguments parser
    parser = argparse.ArgumentParser(description='SMPT Benchmark Script')

    parser.add_argument('path_summary',
                        metavar='summary',
                        type=str,
                        help='path to summary .csv file')

    parser.add_argument('path_oracles',
                        metavar='oracles',
                        type=str,
                        help='path to oracles directory')

    parser_results = parser.parse_args()

    with open(parser_results.path_summary) as csvfile:
        summary_reader = csv.reader(csvfile)

        total_correct_values, total_error_values = 0, 0

        for row in summary_reader:

            examination = None
            if row[2] == 'ReachabilityCardinality':
                examination = 'RC'
            if row[2] == 'ReachabilityFireability':
                examination = 'RF'

            if examination is not None:
                input = row[1]
                results = row[6].split(' ')

                if results[0] != '16':
                    continue

                results.pop(0)
                results = [value.split(':')[1] for value in results]

                try:
                    with open('{}/{}-{}.out'.format(parser_results.path_oracles, input, examination)) as fp_oracles:
                        oracles = fp_oracles.readlines()
                        oracles.pop(0)
                    fp_oracles.close()
                except FileNotFoundError as e:
                    continue

                correct_values, error_values = 0, 0
                for index, result in enumerate(results):
                    if result == '?':
                        continue

                    if result == oracles[index].split(' ')[2]:
                        correct_values += 1
                    else:
                        error_values += 1
                
                print(input, examination, correct_values, '/', error_values)
                total_correct_values += correct_values
                total_error_values += error_values

        print('-------------------------------')
        print(total_correct_values, '/', total_error_values)


if __name__ == "__main__":
    main()
    print("DONE")
    exit(0)
