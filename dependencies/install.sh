#!/bin/env bash

# Installation script for the FM2023 artifact.


echo "Please make sure you have Python 3.7.12 (you may use pyenv)"
echo ""

echo "Please make sure the following packages are installed:"
echo "- automake"
echo "- libtool"

echo ""

echo "Installing z3"
wget --progress=dot:mega https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/z3-4.4.1-x64-ubuntu-14.04.zip
unzip z3-4.4.1-x64-ubuntu-14.04.zip
rm z3-4.4.1-x64-ubuntu-14.04.zip
echo "Done"
echo ""

echo "Installing Tina toolbox"
wget --progress=dot:mega https://projects.laas.fr/tina/binaries/tina-3.7.0-amd64-linux.tgz
tar xvf tina-3.7.0-amd64-linux.tgz
rm tina-3.7.0-amd64-linux.tgz
echo "Done"
echo ""

echo "Installing latte-distro"
wget --progress=dot:mega -O latte-distro-version_1_7_5.zip https://github.com/latte-int/latte-distro/archive/refs/tags/version_1_7_5.zip
unzip latte-distro-version_1_7_5.zip
rm latte-distro-version_1_7_5.zip
cd latte-distro-version_1_7_5
chmod +x autogen.sh
./autogen.sh
./autogen.sh
./configure
make
rm ../../ltmain.sh 2> /dev/null
cd ..
echo "Done"
echo ""

echo "Please add the following lines in your .bashrc:"
SCRIPTPATH="$( cd "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
echo "export PATH=${SCRIPTPATH}/latte-distro-version_1_7_5/dest/bin:\$PATH"
echo "export PATH=${SCRIPTPATH}/tina-3.7.0/bin:\$PATH"
echo "export PATH=${SCRIPTPATH}/z3-4.4.1-x64-ubuntu-14.04/bin:\$PATH"
echo "export LD_LIBRARY_PATH=${SCRIPTPATH}/latte-distro-version_1_7_5/dest/lib:\$LD_LIBRARY_PATH"

echo "Done"

