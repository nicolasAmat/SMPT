#!/bin/bash

# Script to reduce, run analysis, and analyze data for a given list of instances.
# (Without SMPT parallel executions.)


# Get list of instances
LIST=$1

echo "Run reductions"
./run_reductions.sh $1

echo "Run analysis (sequential mode)"
./run_analysis_sequential.sh $1

echo "Convert .out files to .csv"
./out2csv.py "OUTPUTS/" "oracle/" --merge-files

echo "Start Jupyter notebook"
jupyter notebook

# Exit
echo DONE
exit 0
