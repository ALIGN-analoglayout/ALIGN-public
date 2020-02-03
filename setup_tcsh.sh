#
# Source this into your CSH or TCSH shell

setenv ALIGN_HOME $PWD
setenv ALIGN_WORK_DIR $ALIGN_HOME/work

setenv LP_DIR $ALIGN_HOME/lpsolve
setenv BOOST_LP $ALIGN_HOME/boost
setenv JSON $ALIGN_HOME/json
setenv GTEST_DIR $ALIGN_HOME/googletest/googletest/
setenv VENV $ALIGN_HOME/general

if ( ! $?LD_LIBRARY_PATH ) then
        setenv LD_LIBRARY_PATH ""
else
        setenv LD_LIBRARY_PATH "${LD_LIBRARY_PATH}:"
endif
setenv LD_LIBRARY_PATH ${LD_LIBRARY_PATH}${LP_DIR}/lp_solve_5.5.2.5_dev_ux64/

source $VENV/bin/activate.csh
