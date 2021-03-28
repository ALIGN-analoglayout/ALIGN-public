#!/bin/bash

(cd ../../../CellFabric/JSONtoGDS/GDSWriter; tar cvf - *.gds) | docker run --mount source=gdsVol,target=/routerResult -i ubuntu bash -c "cd /routerResult && tar xvf -"

docker run --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=gdsVol,target=/routerResult darpaalign/klayout bash -c klayout
