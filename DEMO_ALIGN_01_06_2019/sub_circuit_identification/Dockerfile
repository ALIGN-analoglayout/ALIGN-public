FROM ubuntu:18.04 as with_python
RUN apt-get update && apt-get install -yq pkg-config python3 python3-pip python3-venv


## Installation of required packages

FROM python:3
RUN pip install matplotlib
RUN pip install pytest-cov 
RUN pip install sympy 
RUN pip install networkx 
RUN pip install graphviz 
RUN pip install coverage
RUN pip install PyYAML
RUN pip install numpy
RUN pip install scipy

### Commands to copy local files into docker environment

COPY . /DEMO1/
#WORKDIR /DEMO1







