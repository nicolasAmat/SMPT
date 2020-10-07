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
    if [[ ($D == GPPP-PT-C0010N1000000000) || ($D == LamportFastMutEx-PT-*) ||  ($D == FamilyReunion-PT-L00200M0020C010P010G005) || ($D == FamilyReunion-PT-L00400M0040C020P020G001) || ($D == ViralEpidemic-PT-S16D2C4A03) ]]; then
        rm -rv $D
    elif [ -d $D ]; then
        echo $D
        cd $D
        rm -v !(model.pnml|ReachabilityCardinality.xml|ReachabilityFireability.xml)
        if [[ ($D == IBM*) ]]; then
            sed -i 's/__/&&/g' ReachabilityCardinality.xml ReachabilityFireability.xml
            sed -i 's/_/./g' ReachabilityCardinality.xml ReachabilityFireability.xml
            sed -i 's/&&/__/g' ReachabilityCardinality.xml ReachabilityFireability.xml
        elif [[ ($D == HypertorusGrid*) || ($D == IOTPpurchase*) || ($D == NeighborGrid*) ]]; then
            sed -i 's/_/./g' ReachabilityCardinality.xml ReachabilityFireability.xml
        elif [[ ($D == Angiogenesis*) ]]; then
            sed -i 's/t0/k0/g' ReachabilityFireability.xml
            sed -i 's/t1/k1/g' ReachabilityFireability.xml
        elif [[ ($D == NeoElection*) ]]; then
            sed -i 's/P-//g' ReachabilityCardinality.xml
            sed -i 's/T-//g' ReachabilityFireability.xml
        elif [[ ($D == Solitaire*) ]]; then
            sed -i 's/p23/T23/g' ReachabilityCardinality.xml
            sed -i 's/p25/T25/g' ReachabilityCardinality.xml
        fi
        ndrio model.pnml model.net
        if [[ ($D == IOTIOTPpurchase*) ]]; then
            sed -i 's/,/./g' model.net
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
