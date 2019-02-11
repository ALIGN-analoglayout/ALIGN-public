FROM cktgen as tally

RUN \
    mkdir -p /scripts

ADD __G1 __G2 /scripts/

ADD *.py /scripts/

ADD satplacer/ /satplacer/

RUN \
    bash -c "source sympy/bin/activate && cd /satplacer/ && pip install ." && \
    rm -r /satplacer














