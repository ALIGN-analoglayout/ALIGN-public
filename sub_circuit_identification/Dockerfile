FROM ubuntu:18.04 as with_python

RUN apt-get update && apt-get install -yq pkg-config python3 python3-pip python3-venv git vim build-essential graphviz libgraphviz-dev protobuf-compiler && apt-get clean

RUN \
    python3 -m venv general && \
    bash -c "source general/bin/activate; pip install --upgrade pip && pip install wheel && pip install pytest sympy networkx pygraphviz coverage pytest-cov protobuf matplotlib pyyaml"

FROM with_python as topology
 
COPY . /sub_circuit_identification

