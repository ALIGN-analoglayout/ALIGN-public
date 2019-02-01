FROM with_python as pysat

RUN \
    apt-get install zlib1g-dev && \
    bash -c "source sympy/bin/activate && pip install --upgrade pip && pip install --upgrade wheel && pip install python-sat"

FROM pysat as tally

RUN \
    mkdir -p /scripts

ADD *.py __G1 __G2 /scripts/















