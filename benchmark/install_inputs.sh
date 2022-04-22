#!/bin/bash

# Script to install INPUTS and oracles from MCC.

# Thanks to Yann Thierry-Mieg.
# This file is inspired from https://github.com/yanntm/pnmcc-models-2021/install_inputs.sh.
# Dependencies:
# - http://mcc.lip6.fr/2021/archives/mcc2021-input.vmdk.tar.bz2
# - https://github.com/yanntm/pnmcc-models-2021


# Enable extended globbing
shopt -s extglob

# Delete old files and directories
rm -rv INPUTS/ 2> /dev/null
rm -rv oracles 2> /dev/null

# Get 2021 MCC models and properties
mkdir INPUTS
wget --no-check-certificate --progress=dot:mega http://mcc.lip6.fr/2021/archives/mcc2021-input.vmdk.tar.bz2
tar -xvjf mcc2021-input.vmdk.tar.bz2
./bin/7z e mcc2021-input.vmdk
./bin/ext2rd 0.img ./:INPUTS
rm -f *.vmdk 0.img *.bz2 1

# Extract archives and remove useless files
cd INPUTS/
rm -rv lost+found
ls *.tgz | xargs -n1 tar -xzvf
rm -v *.tgz
for D in *; do
    if [ -d $D ]; then
        echo $D
        cd $D
        rm -v !(model.pnml|ReachabilityCardinality.xml|ReachabilityFireability.xml)
        cd ..
    fi
done
cd ..

# Get oracles
wget https://yanntm.github.io/pnmcc-models-2021/oracle.tar.gz
tar -xzvf oracle.tar.gz
rm oracle.tar.gz

# Remove useless files
cd oracle/
rm -v !(*-RC.out|*-RF.out|*-RD.out)
cd ..

# Disable extended globbing
shopt -u extglob

# Exit
echo DONE
exit 0
