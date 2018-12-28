#!/bin/bash


for i in mirrors diffpairs1x diffpairs2x diffpairs4x
do
  python placer_equalizer.py -n $i
  mv __json $i.json
done
