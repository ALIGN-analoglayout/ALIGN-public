###################################
#
# Shared build arguments
#
###################################
ARG http_proxy=$http_proxy
ARG https_proxy=$https_proxy
ARG ALIGN_USER=root
ARG ALIGN_BUILD_DIR=/ALIGN-builder
ARG ALIGN_DEPLOY_DIR=/ALIGN-public

####################################
#
# align_builder starts here
#
# (Build align using install.sh)
#
####################################

FROM ubuntu:18.04 as align_builder

# import global args
ARG http_proxy
ARG https_proxy
ARG ALIGN_USER
ARG ALIGN_BUILD_DIR
ARG ALIGN_DEPLOY_DIR

# Set environment variables
SHELL ["/bin/bash", "-c"]
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy
ENV ALIGN_HOME=$ALIGN_BUILD_DIR
ENV USER=$ALIGN_USER
WORKDIR $ALIGN_HOME

# Install ALIGN dependencies
# Note: 1. To promote layer caching, we only copy files needed by
#          `install.sh --deps-only` at this stage
#       2. Only dynamically linked library paths (*.so files)
#          are copied over to $ALIGN_DEPLOY_DIR
#       3. VENV is directly installed ALIGN_DEPLOY_DIR instead
#          of copying by sourcing setup.sh & modifying $VENV
COPY setup.sh install.sh setup.py ./
RUN \
    # Create placeholder files to satisfy pip dependencies
    touch README.md \
    && mkdir -p align \
    && touch align/__init__.py \
    # Avoid copying virtualenv by hacking VENV path
    && source ./setup.sh \
    && export VENV=$ALIGN_DEPLOY_DIR/${VENV#$ALIGN_HOME} \
    # Actual dependency installation happens here
    && source ./install.sh --deps-only \
    # Copy dynamically linked library paths
    && cd $ALIGN_HOME \
    && cp -r --parents .${GTEST_DIR#$ALIGN_HOME}/mybuild/lib $ALIGN_DEPLOY_DIR/ \
    && cp -r --parents .${LP_DIR#$ALIGN_HOME}/lp_solve_5.5.2.5_dev_ux64 $ALIGN_DEPLOY_DIR/

# Install PnR
COPY PlaceRouteHierFlow PlaceRouteHierFlow
RUN \
    # Build PnR
    source setup.sh \
    && export VENV=$ALIGN_DEPLOY_DIR/${VENV#$ALIGN_HOME} \
    && source setup.sh \
    && cd PlaceRouteHierFlow \
    && make \
    # Copy library files & executables
    && cd $ALIGN_HOME \
    && find ./PlaceRouteHierFlow \
        -regex '\(.*\.\(a\|o\|so\)\|.*/unit_tests\|.*/pnr_compiler\)' \
        -exec cp --parents {} $ALIGN_DEPLOY_DIR/ \;

####################################
#
# align_image starts here
# (Copy deps from align_builder)
#
# Note: We (somewhat) optimize image
#       size here
#
####################################
FROM ubuntu:18.04 as align_image

# import global args
ARG http_proxy
ARG https_proxy
ARG ALIGN_USER
ARG ALIGN_BUILD_DIR
ARG ALIGN_DEPLOY_DIR

# Set environment variables
SHELL ["/bin/bash", "-c"]
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy
ENV ALIGN_HOME=$ALIGN_DEPLOY_DIR
ENV USER=$ALIGN_USER
WORKDIR $ALIGN_HOME

RUN apt-get -qq update && apt-get -qq --no-install-recommends install \
        python3 \
        python3-pip \
        make \
        xvfb \
        lcov \
    && rm -rf /var/lib/apt/lists/*

COPY --from=align_builder $ALIGN_HOME .

COPY . .

RUN source setup.sh \
    && pip install -e .
