####################################
#
# align_base starts here
#
####################################
FROM ubuntu:18.04 as align_base

#
# Set shared environment variables
#
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy

#
# We are relying on setup.sh to propagate these
#
ENV ALIGN_HOME=/ALIGN-public
# Begin Note PM: Suboptimal Implementation
ENV GTEST_DIR=$ALIGN_HOME/googletest/googletest
ENV LP_DIR=$ALIGN_HOME/lpsolve
# End Note PM: Suboptimal Implementation

ENV USER=root
WORKDIR $ALIGN_HOME
SHELL ["/bin/bash", "-c"]

####################################
#
# align_builder starts here
#
# (Build align using install.sh)
#
# Note: We optimize cache reuse
#       instead of image size here
#       + Impossible to optimize
#       anyway using install.sh
#
####################################

FROM align_base as align_builder

# Install ALIGN dependencies
# Note: - We copy (or create placeholders for) only those files
#         that are needed by install.sh --deps-only to enable
#         docker layer caching of this stage
COPY setup.sh install.sh setup.py ./
RUN touch README.md && \
    mkdir -p align && \
    touch align/__init__.py && \
    source ./install.sh --deps-only

# Real work gets done here
COPY PlaceRouteHierFlow PlaceRouteHierFlow
RUN source setup.sh && \
        cd PlaceRouteHierFlow && \
        make

# Note: We never install the python component here
#       as installation is instantaeneous
#       as it is most likely to change

####################################
#
# align_image starts here
# (Copy deps from align_builder)
#
# Note: We (somewhat) optimize image
#       size here
#
####################################
FROM align_base as align_image

RUN apt-get -qq update && apt-get -qq --no-install-recommends install \
        python3 \
        python3-pip \
        make \
        xvfb \
        lcov \
    && rm -rf /var/lib/apt/lists/*

# Begin Note PM: Suboptimal Implementation
# (Creating too many layers)
COPY --from=align_builder $GTEST_DIR/mybuild/lib $GTEST_DIR/mybuild/lib
COPY --from=align_builder $LP_DIR/lp_solve_5.5.2.5_dev_ux64 $LP_DIR/lp_solve_5.5.2.5_dev_ux64
COPY --from=align_builder $ALIGN_HOME/general $ALIGN_HOME/general
COPY --from=align_builder $ALIGN_HOME/PlaceRouteHierFlow $ALIGN_HOME/PlaceRouteHierFlow

COPY . .
RUN set -ex && \
    source setup.sh && \
    pip install -e .

# End Note PM: Suboptimal Implementation

#
# Note PM: A better implementation (Not supported by docker 19.03.13)
#
# Once docker version gets updated you can remove a lot of redundant steps and do
#   everything in one step (Tested on Docker 20.10.2)
# (Look for comments saying `Note PM: Suboptimal Implementation' on what to remove)
#
# COPY . .
# RUN --mount=type=bind,src=/ALIGN-public,dst=/ALIGN-src,from=align_builder \
#         set -ex && \
#         source setup.sh && \
#         cd /ALIGN-src && \
#         cp -r --parents .${GTEST_DIR#$ALIGN_HOME}/mybuild/lib $ALIGN_HOME/ && \
#         cp -r --parents .${LP_DIR#$ALIGN_HOME}/lp_solve_5.5.2.5_dev_ux64 $ALIGN_HOME/ && \
#         cp -r --parents .${VENV#$ALIGN_HOME} $ALIGN_HOME/ && \
#         find ./PlaceRouteHierFlow -regex '\(.*\.\(a\|o\|so\)\|.*/unit_tests\|.*/pnr_compiler\)' \
#             -exec cp --parents {} $ALIGN_HOME/ \; && \
#         cd $ALIGN_HOME && \
#         source setup.sh && \
#         pip install -e .
#
# End Note PM: A better implementation (Not supported by docker 19.03.13)
