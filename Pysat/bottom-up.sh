#!/bin/bash

for i in dp1x dp2x dp4x mirrors
do
    ./flow-${i}.sh
done

for i in ctle wcap comp diff lane top
do
    ./flow-${i}.sh --script ${i}.py
done















