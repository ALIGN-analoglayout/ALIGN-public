FROM darpaalign/with_protobuf:2019sept30 as placeroute_image

RUN \
    git clone https://www.github.com/ALIGN-analoglayout/lpsolve.git  && \
    cp -r lpsolve /usr/local/lib/ && \
    apt-get update && \
    apt-get clean

# logger
RUN cd /opt && \
    git clone https://github.com/gabime/spdlog.git && \
    cd spdlog && \
    mkdir build && \
    cd build && \
    cmake CMAKE_INSTALL_MESSAGE=NEVER .. && \
    make -s

COPY . /PlaceRouteHierFlow

ENV LD_LIBRARY_PATH=/usr/local/lib/lpsolve/lp_solve_5.5.2.5_dev_ux64

WORKDIR /PlaceRouteHierFlow

RUN \
    make -j4 -s
