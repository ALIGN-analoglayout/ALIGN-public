#
# Source this (in BASH) to setup a previously installed ALIGN environment
# See install.sh to install the ALIGN environment
#

export ALIGN_HOME=${ALIGN_HOME:-$PWD}
export ALIGN_WORK_DIR=${ALIGN_WORK_DIR:-$ALIGN_HOME/work}

export LP_DIR=${LP_DIR:-$ALIGN_HOME/lpsolve}
#export BOOST_LP=${BOOST_LP:-$ALIGN_HOME/boost}
export JSON=${JSON:-$ALIGN_HOME/json}
export GTEST_DIR=${GTEST_DIR:-$ALIGN_HOME/googletest/googletest}
export SPDLOG_DIR=${SPDLOG_DIR:-$ALIGN_HOME/spdlog}
export SuperLu_DIR=${SuperLu_DIR:-$ALIGN_HOME/superlu}
export VENV=${VENV:-$ALIGN_HOME/general}

if [[ $LD_LIBRARY_PATH != *"$LP_DIR/lp_solve_5.5.2.5_dev_ux64"* && $LD_LIBRARY_PATH != *"$GTEST_DIR/mybuild/lib/"* ]]
then
    export LD_LIBRARY_PATH=${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}$LP_DIR/lp_solve_5.5.2.5_dev_ux64/:$GTEST_DIR/mybuild/lib/
fi

if [[ $PYTHONPATH != *"$ALIGN_HOME/PlaceRouteHierFlow/"* ]]
then
    export PYTHONPATH=${PYTHONPATH:+$PYTHONPATH:}$ALIGN_HOME/PlaceRouteHierFlow/
fi

if [ -f $VENV/bin/activate ]
then
    source $VENV/bin/activate

    echo "ALIGN-public environment is now set up."
    echo "To run a first example, issue the following:"
    echo "   mkdir -p \$ALIGN_WORK_DIR/telescopic_ota"
    echo "   cd \$ALIGN_WORK_DIR/telescopic_ota"
    echo "   schematic2layout.py \$ALIGN_HOME/examples/telescopic_ota -c"
fi