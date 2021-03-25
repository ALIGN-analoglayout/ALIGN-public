#
# Source this (in BASH) to setup a previously installed ALIGN environment
# See install.sh to install the ALIGN environment
#

export ALIGN_HOME=${ALIGN_HOME:-$PWD}
export ALIGN_WORK_DIR=${ALIGN_WORK_DIR:-$ALIGN_HOME/work}
export VENV=${VENV:-$ALIGN_HOME/general}

if [ -f $VENV/bin/activate ]
then
    source $VENV/bin/activate
    echo "ALIGN-public environment is now set up."
    echo "To run a first example, issue the following:"
    echo "   mkdir -p \$ALIGN_WORK_DIR/telescopic_ota"
    echo "   cd \$ALIGN_WORK_DIR/telescopic_ota"
    echo "   schematic2layout.py \$ALIGN_HOME/examples/telescopic_ota -c"
fi