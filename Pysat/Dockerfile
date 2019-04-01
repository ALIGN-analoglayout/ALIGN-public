FROM tally_image as satplacer

RUN \
    mkdir -p /scripts

ADD Pysat/satplacer/ /satplacer/
ADD Cktgen/cktgen/ /cktgen/

RUN \
    bash -c "source general/bin/activate && cd /satplacer/ && pip install . && cd /cktgen && pip install ." && \
    rm -r /satplacer /cktgen

ADD Pysat/*.py /scripts/











