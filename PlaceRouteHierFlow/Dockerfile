FROM with_protobuf as placeroute_image

COPY . /PlaceRouteHierFlow

RUN \
    git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git  && \
    cp -r lpsolve /usr/local/lib/

ENV LD_LIBRARY_PATH=/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64

RUN \
    cd /PlaceRouteHierFlow && make
