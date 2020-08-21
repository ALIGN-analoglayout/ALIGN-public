#
# Source this (in BASH) to setup a previously install ALIGN environment
# See install.sh to install the ALIGN environment
#

export ALIGN_HOME=$PWD
export ALIGN_WORK_DIR=$ALIGN_HOME/work

export LP_DIR=$ALIGN_HOME/lpsolve
export JSON=$ALIGN_HOME/json
export GTEST_DIR=$ALIGN_HOME/googletest/googletest/
export LD_LIBRARY_PATH=${LD_LIBRARY_PATH:+$LD_LIBRARY_PATH:}$ALIGN_HOME/lpsolve/lp_solve_5.5.2.5_dev_ux64/

if [ -z ${NO_VENV+x} ]
then
   if [ -z ${VENV+x} ]
   then
      export VENV=$ALIGN_HOME/general
   fi
   source $VENV/bin/activate
else
   echo "No virtual environment. Python packages installed locally."
fi

echo "ALIGN-public environment is now set up."
echo "To run a first example, issue the following:"
echo "   mkdir -p \$ALIGN_WORK_DIR/telescopic_ota"
echo "   cd \$ALIGN_WORK_DIR/telescopic_ota"
echo "   schematic2layout.py \$ALIGN_HOME/examples/telescopic_ota -c"
