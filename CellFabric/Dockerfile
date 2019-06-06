FROM stevenmburns/pysat_image:2019mar14 as cktgen

COPY /CellFabric /CellFabric/
COPY /GDSConv /GDSConv

RUN \
  bash -c "source general/bin/activate && pip install python-gdsii && cd /GDSConv && pip install . && cd - && cd /CellFabric && pip install ."
