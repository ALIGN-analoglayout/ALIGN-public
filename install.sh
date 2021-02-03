#!/bin/bash
## Run this script starting in the ALIGN-public directory

## Load all environment variables
## (You may wish to override ALIGN_WORK_DIR)

cwd=$PWD

source setup.sh

# Attempt to speed up Make
NB_CORES=$(grep -c '^processor' /proc/cpuinfo)
export MAKEFLAGS="-j$((NB_CORES+1)) -l${NB_CORES}"

### Helper function to git clone only when needed ###
function git_clone () {
    local url="$1"
    local dir="$(basename $url .git)"
    if [ ! -d $dir ] ; then
        git clone --depth 1 $url
    else
        cd $dir
        git pull
        cd -
    fi
}

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

if [[ "$*" != *"--no-deps"* ]]
then

    #### Install Packages
    $SUDO apt-get update && $SUDO apt-get install -yq \
        python3 \
        python3-pip \
        python3-venv \
        python3-dev \
        g++\
        cmake \
        libboost-container-dev \
        graphviz \
        gnuplot \
        curl \
        xvfb \
        gfortran \
        lcov \
    &&  $SUDO apt-get clean

    #### Install klayout 
    curl -k -o ./klayout_0.26.3-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.26.3-1_amd64.deb
    $SUDO apt-get install -yq ./klayout_0.26.3-1_amd64.deb
    rm ./klayout_0.26.3-1_amd64.deb
    #** WSL users would need to install Xming for the display to work

    #### Install lpsolve
    git_clone https://www.github.com/ALIGN-analoglayout/lpsolve.git

    ####  Install json
    git_clone https://github.com/nlohmann/json.git

    #### Install boost (don't need to; already installed using libboost-container-dev above 
    #git clone --recursive https://github.com/boostorg/boost.git
    #cd $ALIGN_HOME/boost
    #./bootstrap.sh -prefix=$ALIGN_HOME/boost
    #./b2 headers

    #### Install googletest
    cd $ALIGN_HOME
    git_clone https://github.com/google/googletest
    cd googletest/
    cmake CMakeLists.txt
    make
    cmake -DBUILD_SHARED_LIBS=ON CMakeLists.txt
    make
    mkdir -p googletest/mybuild
    cp -r lib googletest/mybuild/.

    #### Install logger
    cd $ALIGN_HOME
    git_clone https://github.com/gabime/spdlog.git
    cd spdlog && mkdir -p build && cd build
    cmake .. && make

    ### Install superLU // this now is not correct
    #version 1
    cd $ALIGN_HOME
    git_clone https://www.github.com/ALIGN-analoglayout/superlu.git
    cd superlu
    tar xvfz superlu_5.2.1.tar.gz
    cd SuperLU_5.2.1/
    mkdir -p build
    cd build
    cmake ..
    make

    ## Install pip dependencies
    cd $ALIGN_HOME
    python3 -m venv $VENV
    source $VENV/bin/activate
    python -m pip install --upgrade pip
    python -m pip install pytest pytest-cov pytest-timeout coverage-badge
    python setup.py egg_info
    pip install -r *.egg-info/requires.txt
    rm -fr *.egg-info

    # Reset working directory
    cd $cwd
fi

## Install ALIGN
#---------------

if [[ "$*" != *"--deps-only"* ]]
then

    # Activate environment
    cd $ALIGN_HOME
    source $VENV/bin/activate

    # Install ALIGN python packages

    python -m pip install -e .

    ## Install ALIGN_PnR
    cd $ALIGN_HOME/PlaceRouteHierFlow/ && make

    # Reset working directory
    cd $cwd

fi
