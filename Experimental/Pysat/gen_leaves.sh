#!/bin/bash


for i in mirrors dp1x dp2x dp4x
do
  python placer_equalizer.py -n $i
  mv __json $i.json

  python translate.py -n $i
done
