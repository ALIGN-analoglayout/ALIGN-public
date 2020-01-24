#!/bin/bash
## You should use these set of commands from in ALIGN-public directory 
## Set align home and work directory ( You can use any path for work directory)
export ALIGN_HOME=$PWD
export ALIGN_WORK_DIR=$ALIGN_HOME/work

## Install Prerequisite
#### Install Packages
sudo apt-get update && sudo apt-get install -yq \
    python3 \
    python3-pip \
    python3-venv \
    g++\
    cmake \
    libboost-container-dev \
    graphviz \
    gnuplot \
    curl \
    xvfb \
&&  sudo apt-get clean
#### Install klayout 
sudo curl -o /klayout_0.26.3-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.26.3-1_amd64.deb
sudo apt-get install -yq /klayout_0.26.3-1_amd64.deb

#### Install lpsolve
git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git
####  Install json
git clone https://github.com/nlohmann/json.git
#### Install boost
git clone --recursive https://github.com/boostorg/boost.git
cd $ALIGN_HOME/boost
./bootstrap.sh -prefix=$ALIGN_HOME/boost
./b2 headers

#### Install googletest
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

## Install align 

cd $ALIGN_HOME
python3 -m venv $VENV
source $VENV/bin/activate
pip install --upgrade pip
pip install -e .
deactivate

## Install align_PnR
export LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make
cd $ALIGN_HOME
## Run first example
#mkdir $ALIGN_WORK_DIR
#cd $ALIGN_WORK_DIR
#ln -s $ALIGN_HOME/build/Makefile .
### for umn: module load gcc/8.2.0
#make VENV=$VENV
