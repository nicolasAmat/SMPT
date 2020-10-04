#!/bin/bash

# Set paths
PATH_INPUTS="INPUTS/"
PATH_DATA="data/"

# Create data directory if does not exist
mkdir -p "$PATH_DATA"

# Iterate over instances
for D in "$PATH_INPUTS"*; do
    # Check if there is a 'model.net'
    if [[ -f $D/model.net ]]; then
        # Get instance name
        INSTANCE=${D#$PATH_INPUTS}
        
        # Display instance name
        echo $INSTANCE
        
        # Create the instance directory in the data directory if does not exist
        mkdir -p -- $PATH_DATA$INSTANCE

        # Run smpt and redirect the result in 'reduction.out'
        smpt --auto-reduce --display-reduction-ratio --display-time $D/model.net > $PATH_DATA$INSTANCE/reduction.out
    fi
    exit 0
done

# Exit
echo DONE
exit 0
