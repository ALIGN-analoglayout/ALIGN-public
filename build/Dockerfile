FROM ubuntu:18.04

RUN \
    apt-get update && \
    apt-get install -yq docker docker-compose vim make && \
    apt-get clean

WORKDIR /dataVolume

COPY ./build /ALIGN-public/build
COPY ./examples /ALIGN-public/examples
COPY ./pdks/ /ALIGN-public/pdks

RUN \
    mkdir /ALIGN-public/PlaceRouteHierFlow &&\
    mkdir -p /ALIGN-public/build/ThirdParty/Klayout
