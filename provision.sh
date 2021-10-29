#!/bin/bash

sudo apt-get update
sudo apt-get install -y sudo wget python xxd git

mkdir deps && cd deps

# EMP
wget https://raw.githubusercontent.com/emp-toolkit/emp-readme/master/scripts/install.py && python install.py --deps --tool --ot --sh2pc

# EMP C Wrapper
git clone https://github.com/Isweet/emp-c.git
cd emp-c
mkdir build && cd build
cmake .. && make
cp ../src/empc.h /usr/local/include
cp libempc.so /usr/local/lib
cd ../..

# Haskell
wget -qO- https://get.haskellstack.org/ | sh

cd ..
rm -rf deps

echo "Done"
