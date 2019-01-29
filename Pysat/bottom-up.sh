#!/bin/bash

for i in dp1x dp2x dp4x mirrors
do
    ./flow-${i}.sh
    docker run --mount source=equalizerInputVol,target=/INPUT ubuntu bash -c "cd /INPUT && tar cvf - ${i}_interface.json" | tar xvf -
done

for i in ctle wcap comp diff lane top
do
    ./flow-${i}.sh --script ${i}.py
    docker run --mount source=equalizerInputVol,target=/INPUT ubuntu bash -c "cd /INPUT && tar cvf - ${i}_interface.json" | tar xvf -
done















