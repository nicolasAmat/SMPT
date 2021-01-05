#!/bin/bash

# Script to run SMPT for ReachabilityCardinality, ReachabilityFireability and ReachabilityDeadlock properties 
# on a given list of instances with and without net reductions.


# Set timeout
TIMEOUT=120

# Set paths
PATH_INPUTS="INPUTS/"
PATH_OUTPUTS="OUTPUTS/"

# Create ouputs directory if does not exist
mkdir -p $PATH_OUTPUTS

# Get list of instances
LIST=$1

# Create temporary file
TEMP_FILE=$(mktemp)

# Read instances
while IFS= read instance; do

    # Display instance name
    echo $instance

    # Get relative paths
    PATH_INSTANCE="${PATH_INPUTS}${instance}/"
    PATH_OUTPUT="${PATH_OUTPUTS}${instance}/"

    # Create the instance directory in the outputs directory if does not exist
    mkdir -p $PATH_OUTPUT

    # Run smpt
    echo "smpt --display-method --display-time --timeout $TIMEOUT ${PATH_INSTANCE}model.net --xml ${PATH_INSTANCE}ReachabilityCardinality.xml >  ${PATH_OUTPUT}RC_without_reduction.out" >> $TEMP_FILE
    echo "smpt --display-method --display-time --timeout $TIMEOUT ${PATH_INSTANCE}model.net --xml ${PATH_INSTANCE}ReachabilityFireability.xml >  ${PATH_OUTPUT}RF_without_reduction.out" >> $TEMP_FILE
    echo "smpt --display-method --display-time --timeout $TIMEOUT ${PATH_INSTANCE}model.net --deadlock >  ${PATH_OUTPUT}RD_without_reduction.out" >> $TEMP_FILE
    echo "smpt --display-method --display-time --timeout $TIMEOUT ${PATH_INSTANCE}model.net --xml ${PATH_INSTANCE}ReachabilityCardinality.xml --reduce ${PATH_INSTANCE}model_reduced.net >  ${PATH_OUTPUT}RC_with_reduction.out" >> $TEMP_FILE
    echo "smpt --display-method --display-time --timeout $TIMEOUT ${PATH_INSTANCE}model.net --xml ${PATH_INSTANCE}ReachabilityFireability.xml --reduce ${PATH_INSTANCE}model_reduced.net >  ${PATH_OUTPUT}RF_with_reduction.out" >> $TEMP_FILE
    echo "smpt --display-method --display-time --timeout $TIMEOUT ${PATH_INSTANCE}model.net --deadlock --reduce ${PATH_INSTANCE}model_reduced.net >  ${PATH_OUTPUT}RD_with_reduction.out" >> $TEMP_FILE

done <$LIST

# Run computations in parallel
cat $TEMP_FILE | xargs -t -L 1 -I CMD -P 6 bash -c CMD

# Remove temporary files
rm $TEMP_FILE

# Exit
echo DONE
exit 0
