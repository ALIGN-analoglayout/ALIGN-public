FROM cktgen as satplacer

RUN \
    mkdir -p /scripts

ADD satplacer/ /satplacer/

RUN \
    bash -c "source sympy/bin/activate && cd /satplacer/ && pip install ." && \
    rm -r /satplacer

ADD *.py /scripts/











