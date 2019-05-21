FROM stevenmburns/pysat_image:2019mar14 as cktgen

COPY . /src/

RUN \
  bash -c "source general/bin/activate && cd /src && pip install ."
