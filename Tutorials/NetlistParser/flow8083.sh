#!/bin/bash

docker volume rm -f placerInputVol2
docker volume rm -f inputVol2

(cd ../Placement/testcase; tar cvf - .) | docker run -i --rm --mount source=placerInputVol2,target=/Placement/INPUT ubuntu bash -c "cd /Placement/INPUT; tar xvf -"

docker run --rm --mount source=placerInputVol2,target=/Placement/INPUT placer_image bash -c "cd /Placement && ./placer INPUT/n3.blocks INPUT/n3.nets INPUT/n3.const INPUT/n3.pl INPUT/n3.plt"

docker run --rm --mount source=placerInputVol2,target=/Placement/INPUT --mount source=inputVol2,target=/Viewer/INPUT netlistparser bash -c "source /sympy/bin/activate && cd /NetlistParser && python parse.py -n n3 -id /Placement/INPUT -j /Viewer/INPUT/mydesign_dr_globalrouting.json"

docker run --rm --mount source=inputVol2,target=/public/INPUT -p8083:8000 -d viewer_image /bin/bash -c "source /sympy/bin/activate; cd /public; python -m http.server"

