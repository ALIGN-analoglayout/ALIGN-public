FROM tally_image as satplacer

RUN \
    mkdir -p /scripts

COPY Pysat/satplacer/ /satplacer/
COPY Cktgen/cktgen/ /cktgen/

RUN \
    bash -c "source general/bin/activate && cd /satplacer/ && pip install . && cd /cktgen && pip install ." 

COPY Pysat/*.py /scripts/
