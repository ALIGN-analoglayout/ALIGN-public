#
# Base container starts here
#
FROM ubuntu:18.04 as align_base_using_install

#
# Set required environment variables
#
ENV http_proxy=$http_proxy
ENV https_proxy=$https_proxy

ENV ALIGN_HOME=/ALIGN-public

COPY . $ALIGN_HOME

RUN /bin/bash -c "cd $ALIGN_HOME && source install.sh"
