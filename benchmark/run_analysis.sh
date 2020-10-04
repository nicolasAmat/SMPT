#!/bin/bash

# Set timeout
TIMEOUT=2

# Set paths
PATH_INPUTS="INPUTS/"
PATH_OUTPUTS="OUTPUTS/"

# Create ouputs directory if does not exist
mkdir -p "$PATH_OUTPUTS"

# Get instances list
LIST=$1

# Read instances
while IFS= read instance; do

    # Display instance name
    echo $instance

    # Get relative paths
    PATH_INSTANCE=$PATH_INPUTS$instance
    PATH_OUTPUT=$PATH_OUTPUTS$instance

    # Create the instance directory in the outputs directory if does not exist
    mkdir -p -- $PATH_OUTPUT

    # Run smpt
    smpt --display-method --display-time --timeout $TIMEOUT $PATH_INSTANCE/model.net --xml $PATH_INSTANCE/ReachabilityCardinality.xml >  $PATH_OUTPUT/RC.out &
    P1=$!
    smpt --display-method --display-time --timeout $TIMEOUT $PATH_INSTANCE/model.net --xml $PATH_INSTANCE/ReachabilityFireability.xml >  $PATH_OUTPUT/RF.out &
    P2=$!
    smpt --display-method --display-time --timeout $TIMEOUT $PATH_INSTANCE/model.net --deadlock >  $PATH_OUTPUT/RD.out &
    P3=$!
    smpt --display-method --display-time --timeout $TIMEOUT $PATH_INSTANCE/model.net --xml $PATH_INSTANCE/ReachabilityCardinality.xml --auto-reduce >  $PATH_OUTPUT/RC.out &
    P4=$!
    smpt --display-method --display-time --timeout $TIMEOUT $PATH_INSTANCE/model.net --xml $PATH_INSTANCE/ReachabilityFireability.xml --auto-reduce >  $PATH_OUTPUT/RF.out &
    P5=$!
    smpt --display-method --display-time --timeout $TIMEOUT $PATH_INSTANCE/model.net --deadlock --auto-reduce >  $PATH_OUTPUT/RD.out &
    P6=$!
    wait $P1 $P2 $P3 $P4 $P5 $P6 

done <$LIST


echo DONE
exit 0