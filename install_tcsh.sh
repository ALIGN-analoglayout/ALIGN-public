#!/bin/bash
## Use these set of commands from ALIGN-public directory 
## Set ALIGN_HOME and ALIGN_WORK_DIR directory ( You can use any path for work directory)

setenv ALIGN_HOME $PWD
setenv ALIGN_WORK_DIR $ALIGN_HOME/work

setenv SUDO sudo
#setenv SUDO

## Install Prerequisite
#-----------------------

#### Install Packages
$SUDO yum update && $SUDO yum install -yq \
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
&&  $SUDO yum clean

#### Install klayout 
$SUDO curl -o /klayout-0.26.3-0.x86_64.rpm https://www.klayout.org/downloads/CentOS_7/klayout-0.26.3-0.x86_64.rpm
$SUDO yum install -yq /klayout-0.26.3-0.x86_64.rpm
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

cmake -DCMAKE_CXX_COMPILER=/apps/common/gcc/8.2.0/bin/g++ -DCMAKE_C_COMPILER=/apps/common/gcc/8.2.0/bin/gcc CMakeLists.txt
#cmake CMakeLists.txt
make
cmake -DBUILD_SHARED_LIBS=ON CMakeLists.txt
make
mkdir googletest/mybuild
cp -r lib googletest/mybuild/.

#### Install logger
cd $ALIGN_HOME
git clone https://github.com/gabime/spdlog.git
cd spdlog && mkdir build && cd build
cmake .. && make -j

### Install superLU
cd $ALIGN_HOME
mkdir superlu
cd superlu
wget http://crd-legacy.lbl.gov/~xiaoye/SuperLU/superlu_5.2.1.tar.gz
tar -zxvf superlu_5.2.1.tar.gz

cd SuperLU_5.2.1/
mkdir build
cd build
cmake ..
make -j8

## Set prerequisite paths
#------------------------
setenv LP_DIR $ALIGN_HOME/lpsolve
#setenv BOOST_LP $ALIGN_HOME/boost
setenv JSON $ALIGN_HOME/json
setenv GTEST_DIR $ALIGN_HOME/googletest/googletest/
setenv SPDLOG_DIR $ALIGN_HOME/spdlog
setenv SuperLu_DIR $ALIGN_HOME/superlu
setenv VENV $ALIGN_HOME/general

## install align 
#---------------

# Install ALIGN python packages
cd $ALIGN_HOME
python3 -m venv $VENV
source $VENV/bin/activate.csh
pip install --upgrade pip
pip install -e .
deactivate

## install align_PnR
setenv LD_LIBRARY_PATH $LD_LIBRARY_PATH\:$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/:$GTEST_DIR/mybuild/lib/
cd $ALIGN_HOME/PlaceRouteHierFlow/ && make -j8
cd $ALIGN_HOME

## Run first example
#---------------------
#mkdir $ALIGN_WORK_DIR
#cd $ALIGN_WORK_DIR
#ln -s $ALIGN_HOME/build/Makefile .
#For umn: module load gcc/8.2.0
#make VENV=$VENV
