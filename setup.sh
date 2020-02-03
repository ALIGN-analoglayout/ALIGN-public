#
# Source this into BASH
#

export ALIGN_HOME=$PWD
export ALIGN_WORK_DIR=$ALIGN_HOME/work

export LP_DIR=$ALIGN_HOME/lpsolve
export BOOST_LP=$ALIGN_HOME/boost
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
export VENV=$ALIGN_HOME/general

export LD_LIBRARY_PATH=${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/

source $VENV/bin/activate



