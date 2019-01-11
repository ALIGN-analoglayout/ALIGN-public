FROM with_python

RUN \
    bash -c "source /sympy/bin/activate && pip install cython"

COPY GdsWriter.cpp GdsWriter.h String.h ToString.h gdswriter.pxd gdswriter.pyx gen_gds.py setup.py /src/

RUN \
    bash -c "source /sympy/bin/activate && cd /src && python setup.py build_ext --inplace"
