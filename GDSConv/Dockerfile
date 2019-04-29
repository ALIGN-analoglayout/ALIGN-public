FROM ubuntu:18.04 as gds_image

RUN apt-get update && apt-get install -yq pkg-config python python-pip && apt-get clean
RUN bash -c "rm -rf /var/lib/apt/lists/*"

COPY . /GDSConv

RUN \
    bash -c "pip install python-gdsii"

RUN \
    bash -c "pip install pytest"






