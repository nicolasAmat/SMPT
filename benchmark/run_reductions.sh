#!/bin/bash

# Script to reduce all the instances.

# Set paths
PATH_INPUTS="INPUTS/"
PATH_OUTPUTS="OUTPUTS/"

# Create ouputs directory if does not exist
mkdir -p "$PATH_OUTPUTS"

# Iterate over instances
for D in "$PATH_INPUTS"*; do
    
    # Check if there is a 'model.net'
    if [[ -f $D/model.net ]]; then
        
        # Get instance name
        INSTANCE=${D#$PATH_INPUTS}
        
        # Display instance name
        echo $INSTANCE
        
        # Create the instance directory in the outputs directory if does not exist
        mkdir -p -- $PATH_OUTPUTS$INSTANCE

        # Run smpt and redirect the result in 'reduction.out'
        smpt --auto-reduce --save-reduced-net --display-reduction-ratio --display-time $D/model.net > $PATH_OUTPUTS$INSTANCE/reduction.out
    fi
    exit 0
done

# Exit
echo DONE
exit 0
