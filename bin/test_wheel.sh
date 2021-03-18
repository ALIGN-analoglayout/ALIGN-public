#!/bin/bash
# WARNING: Do not run this file directly!
# Use:
#   docker run -e ALIGN_HOME="$ALIGN_HOME" --rm -v `pwd`:. quay.io/pypa/<<platform>> "$ALIGN_HOME"/bin/build_wheel.sh <<python-tags>>
# Where:
#   platform: manylinux platform (eg. manylinux2010_x86_64)
#   python-tags: python-abi version identifier (eg. cp38-cp38)

set -eo pipefail

export ALIGN_HOME=${ALIGN_HOME:-$PWD}

# Install packages and test
for pyver in "$@"; do
    "/opt/python/${pyver}/bin/pip" install align[test] -f "$ALIGN_HOME"/dist
    "/opt/python/${pyver}/bin/pytest" -n auto -vv --max-worker-restart 0 --dist loadscope "$ALIGN_HOME"/tests
done