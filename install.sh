#!/bin/bash
## Run this script starting in the ALIGN-public directory

## Set ALIGN_HOME and ALIGN_WORK_DIR directory ( You can use any path for work directory)

export ALIGN_HOME=$PWD
export ALIGN_WORK_DIR=$ALIGN_HOME/work

#
# Use sudo if not root; for compatibility with docker
#
if [ $USER = root ]
then
    export SUDO=
else
    export SUDO=sudo
fi

## Install Prerequisite
#-----------------------

#### Install Packages
$SUDO apt-get update && $SUDO apt-get install -yq \
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
&&  $SUDO apt-get clean

#### Install klayout 
curl -o ./klayout_0.26.3-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.26.3-1_amd64.deb
$SUDO apt-get install -yq ./klayout_0.26.3-1_amd64.deb
rm ./klayout_0.26.3-1_amd64.deb
#** WSL users would need to install Xming for the display to work

#### Install lpsolve
git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git
####  Install json
git clone https://github.com/nlohmann/json.git
#### Install boost (don't need to; already installed using libboost-container-dev above 
#git clone --recursive https://github.com/boostorg/boost.git
#cd $ALIGN_HOME/boost
#./bootstrap.sh -prefix=$ALIGN_HOME/boost
#./b2 headers

#### Install googletest
cd $ALIGN_HOME
git clone https://github.com/google/googletest
cd googletest/

cmake CMakeLists.txt
make
mkdir googletest/mybuild
cp -r lib googletest/mybuild/.

#### Install logger
cd $ALIGN_HOME
git clone https://github.com/gabime/spdlog.git
cd spdlog && mkdir build && cd build
cmake .. && make -j

## Set prerequisite paths
#------------------------
export LP_DIR=$ALIGN_HOME/lpsolve
#export BOOST_LP=$ALIGN_HOME/boost
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
export SPDLOG_DIR=$ALIGN_HOME/spdlog
export VENV=$ALIGN_HOME/general

## Install ALIGN
#---------------

# Install ALIGN python packages
cd $ALIGN_HOME
python3 -m venv $VENV
source $VENV/bin/activate
pip install --upgrade pip
pip install -e .
deactivate

## Install ALIGN_PnR
export LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make
cd $ALIGN_HOME

## Run first example
#---------------------
#mkdir $ALIGN_WORK_DIR
#cd $ALIGN_WORK_DIR
#ln -s $ALIGN_HOME/build/Makefile .
### for umn: module load gcc/8.2.0
#make VENV=$VENV
