#!/bin/bash
# WARNING: Do not run this file directly!
#          (Wheels should only be built on manylinux platforms)
# Use:
#   docker run -e ALIGN_HOME="$ALIGN_HOME" --rm -v `pwd`:"$ALIGN_HOME" quay.io/pypa/<<platform>> "$ALIGN_HOME"/bin/build_wheel.sh <<python-tags>>
# Where:
#   platform: manylinux platform (eg. manylinux2010_x86_64)
#   python-tags: python-abi version identifier (eg. cp38-cp38)

set -eo pipefail

export ALIGN_HOME=${ALIGN_HOME:-$PWD}
export ALIGN_WORK_DIR=${ALIGN_WORK_DIR:-$PWD/work}
MAX_JOBS=${MAX_JOBS:-auto}

# Install packages and test
for pyver in "$@"; do
    "/opt/python/${pyver}/bin/python" -m venv .venv
    source .venv/bin/activate
    pip install pip --upgrade
    pip install align[test] -f "$ALIGN_HOME"/dist
    pytest -n "$MAX_JOBS" -vv --max-worker-restart 0 --dist loadscope "$ALIGN_HOME"/tests
done