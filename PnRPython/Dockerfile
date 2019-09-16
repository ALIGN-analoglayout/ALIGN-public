FROM stevenmburns/pysat_image:2019mar14 as cktgen

RUN \
    apt-get update && \
    apt-get install -yq vim &&\
    apt-get clean

COPY /CellFabric /CellFabric/
COPY /GDSConv /GDSConv
COPY /PDK_Abstraction /PDK_Abstraction
COPY /PnRPython /PnRPython

RUN \
  bash -c "source /general/bin/activate && pip install --upgrade pip && pip install python-gdsii && cd /GDSConv && pip install . && cd - && cd /CellFabric && pip install . && cd - && cd PnRPython && pip install . && cd -"
