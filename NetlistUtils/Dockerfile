FROM stevenmburns/pysat_image:2019mar14 as cktgen

COPY /NetlistUtils /NetlistUtils/

RUN \
  bash -c "source general/bin/activate && cd /NetlistUtils && pip install ."
