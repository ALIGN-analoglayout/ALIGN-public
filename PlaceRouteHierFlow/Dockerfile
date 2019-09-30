FROM with_protobuf:latest as placeroute_image

RUN \
    git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git  && \
    cp -r lpsolve /usr/local/lib/ && \
    apt-get update && \
    apt-get install -yq vim && \
    apt-get clean

COPY . /PlaceRouteHierFlow

ENV LD_LIBRARY_PATH=/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64

WORKDIR /PlaceRouteHierFlow

RUN \
    make
