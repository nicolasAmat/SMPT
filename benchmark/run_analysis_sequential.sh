#!/bin/bash

# Script to run SMPT for ReachabilityCardinality, ReachabilityFireability and ReachabilityDeadlock properties 
# on a given list of instances with and without net reductions.
# (Without SMPT parallel executions.)


# Set timeout
TIMEOUT=120

# Set paths
PATH_INPUTS="INPUTS/"
PATH_OUTPUTS="OUTPUTS/"

# Create ouputs directory if does not exist
mkdir -p $PATH_OUTPUTS

# Get list of instances
LIST=$1

# Read instances
while IFS= read instance; do

    # show instance name
    echo $instance

    # Get relative paths
    PATH_INSTANCE="${PATH_INPUTS}${instance}/"
    PATH_OUTPUT="${PATH_OUTPUTS}${instance}/"

    # Create the instance directory in the outputs directory if does not exist
    mkdir -p $PATH_OUTPUT

    # Run smpt
    smpt --show-techniques --show-time --timeout $TIMEOUT "${PATH_INSTANCE}model.net" --xml "${PATH_INSTANCE}ReachabilityCardinality.xml" >  "${PATH_OUTPUT}RC_without_reduction.out"
    smpt --show-techniques --show-time --timeout $TIMEOUT "${PATH_INSTANCE}model.net" --xml "${PATH_INSTANCE}ReachabilityFireability.xml" >  "${PATH_OUTPUT}RF_without_reduction.out"
    smpt --show-techniques --show-time --timeout $TIMEOUT "${PATH_INSTANCE}model.net" --deadlock >  "${PATH_OUTPUT}RD_without_reduction.out"
    smpt --show-techniques --show-time --timeout $TIMEOUT "${PATH_INSTANCE}model.net" --xml "${PATH_INSTANCE}ReachabilityCardinality.xml" --reduce "${PATH_INSTANCE}model_reduced.net" >  "${PATH_OUTPUT}RC_with_reduction.out"
    smpt --show-techniques --show-time --timeout $TIMEOUT "${PATH_INSTANCE}model.net" --xml "${PATH_INSTANCE}ReachabilityFireability.xml" --reduce "${PATH_INSTANCE}model_reduced.net" >  "${PATH_OUTPUT}RF_with_reduction.out"
    smpt --show-techniques --show-time --timeout $TIMEOUT "${PATH_INSTANCE}model.net" --deadlock --reduce "${PATH_INSTANCE}model_reduced.net" >  "${PATH_OUTPUT}RD_with_reduction.out"

done <$LIST

# Exit
echo DONE
exit 0
