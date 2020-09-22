#!/bin/bash

# Thanks to Yann Thierry Mieg, this file is inspired from https://github.com/yanntm/pnmcc-models-2020/install_inputs.sh.
# Dependencies:
# - https://github.com/yanntm/pnmcc-models-2020
# - http://mcc.lip6.fr/archives/mcc2020-input.vmdk.tar.bz2

# Enable extended globbing
shopt -s extglob

# Get 2020 MCC models and properties
mkdir INPUTS
wget --no-check-certificate --progress=dot:mega http://mcc.lip6.fr/archives/mcc2020-input.vmdk.tar.bz2
tar xvjf mcc2020-input.vmdk.tar.bz2
./bin/7z e mcc2020-input.vmdk
./bin/ext2rd 0.img ./:INPUTS
rm -f *.vmdk 0.img *.bz2 1

# Extract archives and remove useless files
cd INPUTS/
rm -v *-COL-*
ls *.tgz | xargs -n1 tar -xzvf
rm -v *.tgz
for D in *; do
    if [ -d "${D}" ]; then
        echo "${D}"
        cd "${D}"
        rm -v !("model.pnml"|"ReachabilityCardinality.xml"|"ReachabilityFireability.xml")
        cd ..
    fi
done
cd ..

# Get oracles made by Yann Thierry Mieg
wget "https://yanntm.github.io/pnmcc-models-2020/oracle.tar.gz"
tar -xzvf "oracle.tar.gz"
rm "oracle.tar.gz"

# Remove useless files
cd oracle/
rm -v *-COL-*
rm -v !(*-RC.out|*-RD.out|*-GP.out)
cd ..

# Disable extended globbing
shopt -u extglob

echo "DONE"
exit 0
