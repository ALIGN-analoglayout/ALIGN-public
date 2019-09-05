FROM ubuntu:18.04

RUN \
    apt-get update && \
    apt-get install -yq docker docker-compose vim make && \
    apt-get clean

WORKDIR /dataVolume

COPY ./compose /ALIGN-public/compose
COPY ./examples /ALIGN-public/examples
COPY ./PDK_Abstraction/ /ALIGN-public/PDK_Abstraction

RUN \
    mkdir /ALIGN-public/PlaceRouteHierFlow &&\
    mkdir -p /ALIGN-public/Build/ThirdParty/Klayout &&\
    mkdir /ALIGN-public/sub_circuit_identification
