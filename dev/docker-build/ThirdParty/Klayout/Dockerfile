FROM ubuntu:18.04 as curl

RUN apt-get update && apt-get install -yq curl && vim git apt-get clean

FROM curl as klayout1

RUN \
    curl -o /klayout_0.25.4-1_amd64.deb https://www.klayout.org/downloads/Ubuntu-18/klayout_0.25.4-1_amd64.deb

FROM klayout1 as klayout

RUN \
    apt-get install -yq /klayout_0.25.4-1_amd64.deb
