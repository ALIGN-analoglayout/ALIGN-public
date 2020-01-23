#!/bin/bash
## You should use these set of commands from in ALIGN-public directory 
## Set align home and work directory ( You can use any path for work directory)
export ALIGN_HOME=$PWD
export ALIGN_WORK_DIR=$ALIGN_HOME/work

## Install Prerequisite
#### install lpsolve
git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git
####  install json
git clone https://github.com/nlohmann/json.git
#### install boost
git clone --recursive https://github.com/boostorg/boost.git
cd $ALIGN_HOME/boost
./bootstrap.sh -prefix=$ALIGN_HOME/boost
./b2 headers

#### install googletest
cd $ALIGN_HOME
git clone https://github.com/google/googletest
cd googletest/
cmake CMakeLists.txt
make
mkdir googletest/mybuild
cp -r lib googletest/mybuild/.

## Set prerequisite path 
export LP_DIR=$ALIGN_HOME/lpsolve
export BOOST_LP=$ALIGN_HOME/boost
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
export VENV=$ALIGN_HOME/general

## install align 

cd $ALIGN_HOME
python3.6 -m venv $VENV
source $VENV/bin/activate
pip install --upgrade pip
pip install -e .
deactivate

## install align_PnR
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make

## Run first example
mkdir $ALIGN_WORK_DIR
cd $ALIGN_WORK_DIR
ln -s $ALIGN_HOME/build/Makefile .

export LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
make VENV=$VENV
