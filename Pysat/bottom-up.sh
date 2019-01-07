#!/bin/bash

python comp.py && ./flow-comp.sh
python diff.py && ./flow-diff.sh

docker run --mount source=equalizerInputVol,target=/INPUT ubuntu bash -c "cd /INPUT && tar cvf - ." > ZZZ.tar
(cd QQQ1; tar xvf ../ZZZ.tar; cp {comp,diff}_interface.json ..)

python lane.py && ./flow-lane.sh
docker run --mount source=equalizerInputVol,target=/INPUT ubuntu bash -c "cd /INPUT && tar cvf - ." > ZZZ.tar

(cd QQQ1; tar xvf ../ZZZ.tar; cp lane_interface.json ..)

python top.py && ./flow-top.sh















