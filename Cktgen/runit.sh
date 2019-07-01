#!/bin/bash


(cd cktgen && pytest --capture=no tests/test_lef_v_to_cktgen.py)

docker run --mount source=equalizerInputVol,target=/INPUT --name sam ubuntu
docker cp cktgen/tests/__json_cktgen_physical_vga sam:INPUT
docker rm sam

docker build -t cktgen .

./flow.sh -sgr -p 8086 -iv equalizerInputVol -ov equalizerOutputVol -s "-m cktgen.cktgen_physical_from_json" -src vga -td ../DetailedRouter/DR_COLLATERAL_Generator/hack84 --placer_json INPUT/__json_cktgen_physical_vga --small --no_interface

