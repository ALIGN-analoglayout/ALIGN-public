#!/bin/bash
## You should use these set of commands from in ALIGN-public directory 
## Set align home and work directory ( You can use any path for work directory)
setenv ALIGN_HOME $PWD
setenv ALIGN_WORK_DIR $ALIGN_HOME/work

## Install Prerequisite
#### Install Packages
sudo yum update && sudo yum install -yq \
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
&&  sudo yum clean
#### klayout 
sudo curl -o /klayout-0.26.3-0.x86_64.rpm https://www.klayout.org/downloads/CentOS_7/klayout-0.26.3-0.x86_64.rpm
sudo yum install -yq /klayout-0.26.3-0.x86_64.rpm

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
#For UMN: cmake -DCMAKE_CXX_COMPILER=/apps/common/gcc/8.2.0/bin/g++ -DCMAKE_C_COMPILER=/apps/common/gcc/8.2.0/bin/gcc CMakeLists.txt
cmake CMakeLists.txt
make
mkdir googletest/mybuild
cp -r lib googletest/mybuild/.

## Set prerequisite path 
setenv LP_DIR $ALIGN_HOME/lpsolve
setenv BOOST_LP $ALIGN_HOME/boost
setenv JSON $ALIGN_HOME/json
setenv GTEST_DIR $ALIGN_HOME/googletest/googletest/
setenv VENV $ALIGN_HOME/general

## install align 

cd $ALIGN_HOME
python3 -m venv $VENV
source $VENV/bin/activate
pip install --upgrade pip
pip install -e .
deactivate

## install align_PnR
setenv LD_LIBRARY_PATH $ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make
cd $ALIGN_HOME

## Run first example
#mkdir $ALIGN_WORK_DIR
#cd $ALIGN_WORK_DIR
#ln -s $ALIGN_HOME/build/Makefile .
### for umn: module load gcc/8.2.0
#make VENV=$VENV
