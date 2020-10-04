#!/bin/bash

# Script to install INPUTS and oracles from MCC.

# Thanks to Yann Thierry-Mieg.
# This file is inspired from https://github.com/yanntm/pnmcc-models-2020/install_inputs.sh.
# Dependencies:
# - http://mcc.lip6.fr/archives/mcc2020-input.vmdk.tar.bz2
# - https://github.com/yanntm/pnmcc-models-2020

# Enable extended globbing
shopt -s extglob

# Delete old files and directories
rm -rv INPUTS/ 2> /dev/null
rm -v inputs_list 2> /dev/null
rm -rv oracles 2> /dev/null

# Get 2020 MCC models and properties
mkdir INPUTS
wget --no-check-certificate --progress=dot:mega http://mcc.lip6.fr/archives/mcc2020-input.vmdk.tar.bz2
tar -xvjf mcc2020-input.vmdk.tar.bz2
./bin/7z e mcc2020-input.vmdk
./bin/ext2rd 0.img ./:INPUTS
rm -f *.vmdk 0.img *.bz2 1

# Extract archives and remove useless files
cd INPUTS/
rm -v *-COL-*
rm -rv lost+found
ls *.tgz | xargs -n1 tar -xzvf
rm -v *.tgz
for D in *; do
    if [[ ($D == GPPP-PT-C0010N1000000000) || ($D == LamportFastMutEx-PT-*) ]]; then
        rm -rv $D
    elif [ -d $D ]; then
        echo $D
        cd $D
        rm -v !(model.pnml|ReachabilityCardinality.xml|ReachabilityFireability.xml)
        ndrio model.pnml model.net
        if [[ ($D == IBM*) ]]; then
            sed -i 's/_/./g' ReachabilityCardinality.xml ReachabilityFireability.xml
        fi
        cd ..
    fi
done
cd ..

# Get oracles
wget https://yanntm.github.io/pnmcc-models-2020/oracle.tar.gz
tar -xzvf oracle.tar.gz
rm oracle.tar.gz

# Remove useless files
cd oracle/
rm -v *-COL-*
rm -v !(*-RC.out|*-RF.out|*-RD.out)
cd ..

# Disable extended globbing
shopt -u extglob

# Exit
echo DONE
exit 0
