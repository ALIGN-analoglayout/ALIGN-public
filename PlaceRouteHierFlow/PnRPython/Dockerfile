FROM stevenmburns/pysat_image:2019mar14 as cktgen

RUN \
    bash -c "source /general/bin/activate && pip install --upgrade pip"

COPY . /PnRPython/

RUN \
  bash -c "source /general/bin/activate && cd /PnRPython && pip install ."
