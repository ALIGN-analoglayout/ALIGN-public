#!/bin/bash
set -ex

## Run this script starting in the ALIGN-public directory

## Load all environment variables
## (You may wish to override ALIGN_WORK_DIR)

cwd=$PWD

source setup.sh

#
# Use sudo if not root; for compatibility with docker
#
if [ $USER = root ]
then
    export SUDO=
else
    export SUDO=sudo
fi

#### Install Packages
$SUDO apt-get update && $SUDO apt-get install -yq \
    git \
    python3 \
    python3-pip \
    python3-venv \
    python3-dev \
    g++\
    cmake \
    libboost-container-dev \
    graphviz \
    gnuplot \
    xvfb \
    gfortran \
    lcov \
&&  $SUDO apt-get clean

cd $ALIGN_HOME

python3 -m venv $VENV
source $VENV/bin/activate
python -m pip install setuptools wheel pybind11 scikit-build cmake ninja
python -m pip install -e .[test] --no-build-isolation

cd $cwd
