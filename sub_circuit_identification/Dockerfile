FROM ubuntu:18.04 as with_python

RUN apt-get update && apt-get install -yq pkg-config python3 python3-pip python3-venv git build-essential graphviz libgraphviz-dev protobuf-compiler && apt-get clean

RUN \
    python3 -m venv sympy && \
    bash -c "source sympy/bin/activate; pip install pytest sympy networkx pygraphviz coverage pytest-cov protobuf matplotlib"

FROM with_python as topology
 
RUN \
    pip install matplotlib
RUN \
    mkdir -p /DEMO \
    rm  /DEMO/ \
    mkdir -p /DEMO/src \
    mkdir -p /DEMO/circuit_graphs \
    mkdir -p /DEMO/library_graphs \
    mkdir -p results

COPY . /DEMO/

RUN ls -la /DEMO
