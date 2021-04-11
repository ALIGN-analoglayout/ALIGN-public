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

align_root="$ALIGN_HOME"
align_work_root="$ALIGN_WORK_DIR"
# Install packages and test
for pyver in "$@"; do
    current_test_dir="${ALIGN_WORK_DIR}/${pyver}"
    mkdir -p "$current_test_dir"
    cd "$ALIGN_HOME"
    cp -r tests examples pytest.ini conftest.py pdks PlaceRouteHierFlow Viewer "$current_test_dir"
    # All operations in newly created $current_test_dir
    cd "$current_test_dir"
    export ALIGN_HOME="$current_test_dir"
    export ALIGN_WORK_DIR="${current_test_dir}/work"
    "/opt/python/${pyver}/bin/python" -m venv .venv
    source .venv/bin/activate
    pip install pip --upgrade
    pip install align[test] -f "$align_root"/wheelhouse
    pytest -n "$MAX_JOBS" -vv --max-worker-restart 0 tests
    # Reset ALIGN_WORK_DIR
    export ALIGN_WORK_DIR="$align_work_root"
    export ALIGN_HOME="$align_root"
done