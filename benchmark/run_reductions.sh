#!/bin/bash

# Script to reduce a given list of instances.


# Set paths
PATH_INPUTS="INPUTS/"
PATH_OUTPUTS="OUTPUTS/"

# Create ouputs directory if does not exist
mkdir -p $PATH_OUTPUTS

# Get list of instances
LIST=$1

# Read instances
while IFS= read instance; do

    # Check if there is a 'model.net'
    if [[ -f ${PATH_INPUTS}${instance}/model.net ]]; then
        
        # Display instance name
        echo $instance
        
        # Create the instance directory in the outputs directory if does not exist
        mkdir -p -- "${PATH_OUTPUTS}${instance}"

        # Run smpt and redirect the result in 'reduction.out'
        smpt --auto-reduce --save-reduced-net --display-reduction-ratio --display-time "${PATH_INPUTS}${instance}/model.net" > "${PATH_OUTPUTS}${instance}/reduction.out"
    fi

done <$LIST

# Exit
echo DONE
exit 0
