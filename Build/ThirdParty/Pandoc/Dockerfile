FROM sumdoc/texlive-2017

MAINTAINER Ciantic

# Basic and usefull stuff
RUN apt-get update && apt-get install -y -o Acquire::Retries=10 --no-install-recommends \
    build-essential make inkscape wget python-pip python-setuptools python-dev && \
    python -m pip install --upgrade pip && \
    python -m pip install --upgrade setuptools && \
    mkdir -p /installation/ && \
    wget https://github.com/jgm/pandoc/releases/download/2.1.1/pandoc-2.1.1-1-amd64.deb \
        --no-check-certificate \
        -O /installation/pandoc.deb && \
    dpkg -i /installation/pandoc.deb && \
    rm -rf /installation/ && \
    pip install wheel && \
    pip install pandoc-fignos

WORKDIR /source

ENTRYPOINT []
CMD []
