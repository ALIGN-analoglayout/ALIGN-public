#
# Source this (in BASH) to setup a previously install ALIGN environment
# See install.sh to install the ALIGN environment
#

export ALIGN_HOME=$PWD
export ALIGN_WORK_DIR=$ALIGN_HOME/work

export LP_DIR=$ALIGN_HOME/lpsolve
#export BOOST_LP=$ALIGN_HOME/boost
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
export GTEST_DIR=$ALIGN_HOME/spdlog
export VENV=$ALIGN_HOME/general

export LD_LIBRARY_PATH=${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/

source $VENV/bin/activate

echo "ALIGN-public environment is now set up."
echo "To run a first example, issue the following:"
echo "   mkdir -p \$ALIGN_WORK_DIR/telescopic_ota"
echo "   cd \$ALIGN_WORK_DIR/telescopic_ota"
echo "   schematic2layout.py \$ALIGN_HOME/examples/telescopic_ota -c"



