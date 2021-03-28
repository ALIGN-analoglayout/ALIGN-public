#
# Base container starts here
#
FROM ubuntu:20.04 as align_base_using_install

#
# Set required environment variables
#
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy

ENV ALIGN_HOME=/ALIGN-public
WORKDIR $ALIGN_HOME
ENV USER=root
ENV DEBIAN_FRONTEND=noninteractive

# Install ALIGN dependencies
# Note: - We copy (or create placeholders for) only those files
#         that are needed by install.sh --deps-only to enable
#         docker layer caching of this stage
COPY setup.sh .
COPY install.sh .
COPY setup.py .
RUN touch README.md && \
    mkdir -p align && \
    touch align/__init__.py && \
    ./install.sh --deps-only

# Copy source and install align
# Note: Dependencies already installed in previous layer
COPY . .
RUN ./install.sh --no-deps