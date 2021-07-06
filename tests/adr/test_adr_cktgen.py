import json
import os
import pathlib

from align.adr.ad import ADNetlist

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

def test_adr_cktgen():
    
    metal_layer_map = { f'M{i}' : f'metal{i}' for i in range(0,7) }
    via_layer_map = { f'V{i}' : f'via{i}' for i in range(0,6) }
    layer_map = dict(list(metal_layer_map.items()) + list(via_layer_map.items()))


    bn = "foo"

    placer_results = {
        "bbox": [0,0,100,100],
        "instances": [
            {
                "template_name": "a",
                "instance_name": "u0",
                "transformation": { "oX": 0, "oY": 0, "sX": 1, "sY": 1},
                "formal_actual_map": {
                    "inp": "a"
                }
            },
            {
                "template_name": "a",
                "instance_name": "u1",
                "transformation": { "oX": 100, "oY": 0, "sX": 1, "sY": 1},
                "formal_actual_map": {
                    "inp": "a"
                }
            }
        ],
        "leaves": [
            {
                "template_name": "a",
                "bbox": [0,0,100,100],
                "terminals": [
                    {
                        "layer": "M1",
                        "netName": "inp",
                        "rect": [1,1,3,3]
                    }
                ]
            }
        ]
    }

    netl = ADNetlist.fromPlacerResults( bn, layer_map, placer_results)

    assert netl.nm == bn
    assert netl.bbox.toList() == [0,0,100,100]
    assert netl.gidIndex == 2
    assert len(netl.wire_cache) == 2

    assert ('a', (1,1,3,3), 'metal1') in netl.wire_cache

    assert [  0,0,100,100] == netl.instances['u0'].toList()
    assert [100,0,200,100] == netl.instances['u1'].toList()

    assert len(netl.nets) == 1
    print(netl.nets)

