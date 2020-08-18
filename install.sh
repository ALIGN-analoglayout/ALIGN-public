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
$SUDO apt-get update && $SUDO apt-get install -yq libboost-container-dev
$SUDO apt-get update && $SUDO apt-get install -yq \
    python3 \
    python3-pip \
    python3-venv \
    g++\
    cmake \
    libboost-all-dev \
    graphviz \
    gnuplot \
    curl \
    xvfb \
    libx11-dev \
    xorg-dev \
    libglu1-mesa-dev \
    freeglut3-dev \
    libglew1.5 \
    libglew1.5-dev \
    libglu1-mesa \
    libglu1-mesa-dev \
    libgl1-mesa-glx \
    libgl1-mesa-dev \
    lp-solve \
    liblpsolve55-dev \
    libgtest-dev \
&&  $SUDO apt-get clean

#### Install klayout 
curl -o ./klayout_0.26.3-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.26.3-1_amd64.deb
curl -o ./klayout_0.27.7-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-20/klayout_0.26.7-1_amd64.deb
$SUDO apt-get install -yq ./klayout_0.26.3-1_amd64.deb
$SUDO apt-get install -yq ./klayout_0.27.7-1_amd64.deb
rm ./klayout_0.26.3-1_amd64.deb
rm ./klayout_0.27.7-1_amd64.deb
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

## Set prerequisite paths
#------------------------
export LP_DIR=$ALIGN_HOME/lpsolve
#export BOOST_LP=$ALIGN_HOME/boost
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
export VENV=$ALIGN_HOME/align_venv

## Install ALIGN
#---------------

# Install ALIGN python packages
cd $ALIGN_HOME
pip3 install --upgrade pip
pip3 install -e .
python3 -m venv $VENV
source $VENV/bin/activate
pip install --upgrade pip
pip install -e .
deactivate

## Install ALIGN_PnR
export LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make
cd $ALIGN_HOME

# Setup environment variable script for next time:
mkdir $ALIGN_WORK_DIR
ln -s $ALIGN_HOME/build/Makefile .

## Run first example
#---------------------
#cd $ALIGN_WORK_DIR
### for umn: module load gcc/8.2.0
#make VENV=$VENV
