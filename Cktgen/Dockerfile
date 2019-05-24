FROM stevenmburns/pysat_image:2019mar14 as cktgen

COPY cktgen/ /cktgen/

RUN \
  bash -c "source general/bin/activate && cd /cktgen && pip install ."

COPY *.py /Cktgen/
