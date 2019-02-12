FROM with_python as cktgen

ADD cktgen/ /cktgen/

RUN \
  bash -c "source sympy/bin/activate && cd /cktgen && pip install ." && \
  rm -rf /cktgen 
















