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
curl -o ./klayout_0.26.7-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.26.7-1_amd64.deb
$SUDO apt-get install -yq ./klayout_0.26.7-1_amd64.deb
rm ./klayout_0.26.7-1_amd64.deb
#** WSL users would need to install Xming for the display to work

#### Install lpsolve
git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git
####  Install json
git clone https://github.com/nlohmann/json.git

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
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/

## Install ALIGN
#---------------
 
# Install ALIGN python packages
cd $ALIGN_HOME

if [ -z ${NO_VENV+x} ]
then
   if [ -z ${VENV+x} ]
   then
      export VENV=$ALIGN_HOME/general
   fi
   python3 -m venv $VENV
   source $VENV/bin/activate
   pip install --upgrade pip
   pip install -e .
   deactivate
else
   echo "No virtual environment. Python packages installed locally."
   pip3 install --upgrade pip
   pip3 install -e .
fi

## Install ALIGN_PnR
export LD_LIBRARY_PATH=$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make
cd $ALIGN_HOME
