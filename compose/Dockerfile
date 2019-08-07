FROM ubuntu:18.04

RUN \
    apt-get update && \
    apt-get install -yq docker docker-compose vim make && \
    apt-get clean

WORKDIR /dataVolume

COPY . /ALIGN-public

