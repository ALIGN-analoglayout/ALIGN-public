# GDS Viewer

You can use Klayout to view GDS files.
To build it, use:
````
docker build -t darpaalign/klayout .


docker run --env="DISPLAY" --env="QT_X11_NO_MITSHM=1" --volume="/tmp/.X11-unix:/tmp/.X11-unix:rw" --mount source=inputVol,target=/INPUT darpaalign/klayout bash -c "cd /DEMO && klayout"

````
````
Use `./flow.sh` to run the router and view the results.
You need to be on a Linux box for this. Try `xhost +` if you are having trouble. (use:xhost local:root)


#!/bin/bash

docker run --mount source=routerResultVol,target=/routerResult router_image bash -c "cd /Router && ./run.sh && cp top.gds /routerResult"



