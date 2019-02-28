#!/bin/bash

docker run --mount source=routerResultVol,target=/routerResult router_image bash -c "cd /Router && ./run.sh && cp top.gds /routerResult"

docker run --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=routerResultVol,target=/routerResult darpaalign/klayout bash -c klayout
