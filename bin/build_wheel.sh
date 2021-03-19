#!/bin/bash
# WARNING: Do not run this file directly!
# Use:
#   docker run -e ALIGN_HOME=/ALIGN-public --rm -v `pwd`:/ALIGN-public quay.io/pypa/<<platform>> /ALIGN-public/bin/build_wheel.sh <<python-tags>>
# Where:
#   platform: manylinux platform (eg. manylinux2010_x86_64)
#   python-tags: python-abi version identifier (eg. cp38-cp38)

set -eo pipefail

# install some dependencies
case "$AUDITWHEEL_PLAT" in
    "manylinux1_x86_64"|"manylinux2010_x86_64"|"manylinux2014_x86_64")
        yum -y install boost-devel lpsolve
    ;;
    # "manylinux_2_24_x86_64")
    # TODO: Implement this for Python 3.10 support
    #       (PEP600 requires pip >= 20.3)
    *)
        echo "WARNING: Unknown environment."
        echo "Please make sure you are using a supported manylinux platform to run this script"
        exit 1
    ;;
esac

export ALIGN_HOME=${ALIGN_HOME:-$PWD}

function repair_wheel {
    wheel="$1"
    dest="$2"
    if ! auditwheel show "$wheel"; then
        echo "Skipping non-platform wheel $wheel"
    else
        auditwheel repair "$wheel" --plat "$AUDITWHEEL_PLAT" -w "$dest"
    fi
}

# install some dependencies
yum -y install boost boost-devel lpsolve

# Compile all wheels
for pyver in "$@"; do
    "/opt/python/${pyver}/bin/pip" -v wheel "$ALIGN_HOME" -w /tmp/dist/ --no-deps
done

# Bundle external shared libraries into the align wheels
for whl in /tmp/dist/align*.whl; do
    repair_wheel "$whl" "$ALIGN_HOME"/dist/
    rm $whl
done
