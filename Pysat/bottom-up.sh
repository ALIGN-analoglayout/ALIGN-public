#!/bin/bash

for i in dp1x dp2x dp4x mirrors wcap comp diff lane top
do
    python ${i}.py && ./flow-${i}.sh
    docker run --mount source=equalizerInputVol,target=/INPUT ubuntu bash -c 'cd /INPUT && tar cvf - ${i}_interface.json' | tar xvf -
done















