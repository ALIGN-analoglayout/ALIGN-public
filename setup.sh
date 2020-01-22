setenv ALIGN_HOME $PWD
setenv ALIGN_WORK_DIR $ALIGN_HOME/work
git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git
git clone https://github.com/nlohmann/json.git
git clone --recursive https://github.com/boostorg/boost.git
cd $ALIGN_HOME/boost
./bootstrap.sh -prefix=$ALIGN_HOME/boost
./b2 headers
cd $ALIGN_HOME
git clone https://github.com/google/googletest
cd googletest/
cmake -DCMAKE_CXX_COMPILER=/apps/common/gcc/8.2.0/bin/g++ -DCMAKE_C_COMPILER=/apps/common/gcc/8.2.0/bin/gcc CMakeLists.txt
make
mkdir googletest/mybuild
cp -r lib googletest/mybuild/.
cd ../
setenv LP_DIR $ALIGN_HOME/lpsolve
setenv BOOST_LP $ALIGN_HOME/boost
setenv LD_LIBRARY_PATH $ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/
setenv JSON $ALIGN_HOME/json
setenv GTEST_DIR $ALIGN_HOME/googletest/googletest/
python3.6 -m venv general
source general/bin/activate.csh
cd $ALIGN_HOME/PlaceRouteHierFlow/
make
cd ..
pip install -e .
mkdir work
pip install --upgrade pip
pip install wheel pytest general networkx pygraphviz coverage pytest-cov protobuf matplotlib pyyaml python-gdsii
cd $ALIGN_WORK_DIR
ln -s $ALIGN_HOME/build/Makefile .
