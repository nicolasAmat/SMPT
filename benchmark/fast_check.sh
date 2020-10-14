#!/bin/bash

# Script to reduce, run analysis, and analyze data for a given list of instances.


# Get list of instances
LIST=$1

./run_reductions.sh $1
./run_analysis.sh $1
./out2csv.py "OUTPUTS/" "oracles/" --merge-files
jupyter notebook experimental_results.ipynb

# Exit
echo DONE
exit 0
