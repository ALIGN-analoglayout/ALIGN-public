###################################
#
# Shared build arguments
#
###################################
ARG http_proxy=$http_proxy
ARG https_proxy=$https_proxy
ARG ALIGN_USER=root
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
ARG ALIGN_DEPLOY_DIR

# Set environment variables
SHELL ["/bin/bash", "-c"]
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy
ENV ALIGN_HOME=$ALIGN_DEPLOY_DIR
ENV USER=$ALIGN_USER
WORKDIR $ALIGN_HOME

# Install ALIGN dependencies
# Note: To promote layer caching, we only copy files needed by
#           `install.sh --deps-only` at this stage
#       To reduce image size, we remove all files not needed by
#           PnR and then cleanup PnR itself
COPY setup.sh install.sh setup.py ./
RUN \
    # Create placeholder files to satisfy pip dependencies
    touch README.md \
    && mkdir -p align \
    && touch align/__init__.py \
    # Actual dependency installation happens here
    && source ./install.sh --deps-only \
    # Trim down VENV to the essentials
    && find $VENV -depth \
    \( \
        \( -type d -a \( \
            -name test -o -name tests -o -name idle_test \
            -o -name doc -o -name 'python-wheels' \
            -o -name '*.dist-info' -o -name '*.egg-info' \
            -o -name __pycache__ \
        \) \) \
        -o \
        \( -type f -a \( \
            -name '*.pyc' -o -name '*.pyo' \
            -name '*.whl' -o -name '*.a' \
        \) \) \
    \) -exec rm -rf '{}' + \
    # Remove all build dirs not needed by PnR
    && cp -r --parents $LP_DIR/lp_solve_5.5.2.5_dev_ux64 /tmp \
    && cp -r --parents $JSON/include /tmp \
    && cp -r --parents $GTEST_DIR/mybuild/lib /tmp \
    && cp -r --parents $GTEST_DIR/include /tmp \
    && cp -r --parents $SPDLOG_DIR/include /tmp \
    && cp -r --parents $SuperLu_DIR/SuperLU_5.2.1/build /tmp \
    && cp -r --parents $SuperLu_DIR/SuperLU_5.2.1/SRC /tmp \
    && cp -r --parents $SuperLu_DIR/SuperLU_5.2.1/CBLAS /tmp \
    && rm -fr $LP_DIR $JSON $SPDLOG_DIR $SuperLu_DIR \
            $ALIGN_HOME/googletest \
            $ALIGN_HOME/align $ALIGN_HOME/README.md $ALIGN_HOME/setup.py \
    && mv /tmp$ALIGN_HOME/* $ALIGN_HOME/

# Install PnR
COPY PlaceRouteHierFlow PlaceRouteHierFlow
RUN \
    # Source environment vars
    source setup.sh \
    # Build PlaceRouteHierFlow
    && cd $ALIGN_HOME/PlaceRouteHierFlow \
    && make -j4 \
    # Clean up anything we no longer need
    && find . \
        -not \
        -regex '\(.*\.\(so\|gcno\)\|.*/unit_tests\|.*/pnr_compiler\)' \
        -exec rm -f {} \; \
    && rm -fr $LP_DIR/include $GTEST_DIR/include \
            $JSON $SPDLOG_DIR $SuperLu_DIR \
            $ALIGN_HOME/*.sh

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
ARG ALIGN_DEPLOY_DIR

# Set environment variables
SHELL ["/bin/bash", "-c"]
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy
ENV ALIGN_HOME=$ALIGN_DEPLOY_DIR
ENV USER=$ALIGN_USER
WORKDIR $ALIGN_HOME

RUN \
    # Install basic dependencies
    apt-get -qq update \
    && apt-get -qq --no-install-recommends install \
        python3 \
        python3-pip \
        make \
        xvfb \
        lcov \
    # Get Klayout using curl
    && savedAptMark="$(apt-mark showmanual)" \
    && apt-get install -y --no-install-recommends curl \
    && curl -k -o ./klayout_0.26.3-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.26.3-1_amd64.deb \
    && apt-mark auto '.*' > /dev/null \
    && [ -z "$savedAptMark" ] || apt-mark manual $savedAptMark \
    && apt-get purge -y --auto-remove -o APT::AutoRemove::RecommendsImportant=false \
    # Install Klayout
    && apt-get install -yq ./klayout_0.26.3-1_amd64.deb \
    # Clean up
    && rm ./klayout_0.26.3-1_amd64.deb \
    && rm -rf /var/lib/apt/lists/*

COPY --from=align_builder $ALIGN_HOME .

COPY . .

RUN source setup.sh \
    && pip install -e .
