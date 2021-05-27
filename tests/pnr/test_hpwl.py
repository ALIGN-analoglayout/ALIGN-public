import json
import pathlib

from align.pnr.hpwl import gen_netlist, calculate_HPWL_from_placement_verilog_d, Interval, SemiPerimeter
from align.pnr.render_placement import standalone_overlap_checker

def test_interval():
    i = Interval()
    i.add( 7)

    assert 0 == i.dist()

    i.add( 3)

    assert 4 == i.dist()

def test_semiperimeter():
    sp = SemiPerimeter()
    sp.addPoint( (3,7))

    assert 0 == sp.dist()

    sp.addRect( (10,10,12,12))

    assert 14 == sp.dist()


def test_gen_netlist():
    placement_verilog_d = {
        "modules": [
            { "abstract_name": "top",
              "concrete_name": "top",
              "bbox": [0,0,100,100],
              "parameters": [],
              "instances": [
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u0",
                      "transformation": { "oX": 0, "oY": 0, "sX": 1, "sY": 1},
                      "fa_map": [{"formal": "x", "actual": "y"}]
                  },
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u1",
                      "transformation": { "oX": 0, "oY": 20, "sX": 1, "sY": 1},
                      "fa_map": [{"formal": "x", "actual": "y"}]
                  }
              ]
              
            }
        ],
        "leaves": [
            { "abstract_name": "a",
              "concrete_name": "a",
              "bbox": [0,0,10,10],
              "terminals": [
                  { "name": "x",
                    "rect": [4,4,6,6]
                  }
              ]
            }
        ]
    }
    
    nets_d = gen_netlist( placement_verilog_d, 'top')

    assert 24 == calculate_HPWL_from_placement_verilog_d( placement_verilog_d, 'top', nets_d)

def test_gen_netlist_flip():
    placement_verilog_d = {
        "modules": [
            { "abstract_name": "top",
              "concrete_name": "top",
              "bbox": [0,0,100,100],
              "parameters": [],
              "instances": [
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u0",
                      "transformation": { "oX": 0, "oY": 0, "sX": 1, "sY": 1},
                      "fa_map": [{"formal": "x", "actual": "y"}]
                  },
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u1",
                      "transformation": { "oX": 15, "oY": 20, "sX": 1, "sY": 1},
                      "fa_map": [{"formal": "x", "actual": "y"}]
                  }
              ]
              
            }
        ],
        "leaves": [
            { "abstract_name": "a",
              "concrete_name": "a",
              "bbox": [0,0,10,10],
              "terminals": [
                  { "name": "x",
                    "rect": [1,2,3,4]
                  }
              ]
            }
        ]
    }
    
    nets_d = gen_netlist( placement_verilog_d, 'top')

    assert 39 == calculate_HPWL_from_placement_verilog_d( placement_verilog_d, 'top', nets_d)

    placement_verilog_d['modules'][0]['instances'][0]['transformation'] = { "oX": 10, "oY": 0, "sX": -1, "sY": 1}
    assert 33 == calculate_HPWL_from_placement_verilog_d( placement_verilog_d, 'top', nets_d)

    placement_verilog_d['modules'][0]['instances'][0]['transformation'] = { "oX": 10, "oY": 10, "sX": -1, "sY": -1}
    assert 29 == calculate_HPWL_from_placement_verilog_d( placement_verilog_d, 'top', nets_d)

    placement_verilog_d['modules'][0]['instances'][0]['transformation'] = { "oX": 0, "oY": 10, "sX":  1, "sY": -1}
    assert 35 == calculate_HPWL_from_placement_verilog_d( placement_verilog_d, 'top', nets_d)

def test_gen_netlist_matrix():

    txt = """{
  "global_signals": [],
  "leaves": [
    {
      "abstract_name": "slice",
      "bbox": [
        0,
        0,
        800,
        840
      ],
      "concrete_name": "slice_a",
      "terminal_centers": [
        {
          "center": [
            400,
            168
          ],
          "name": "inp"
        },
        {
          "center": [
            400,
            672
          ],
          "name": "out"
        }
      ],
      "terminals": [
        {
          "name": "inp",
          "rect": [
            124,
            152,
            676,
            184
          ]
        },
        {
          "name": "out",
          "rect": [
            124,
            656,
            676,
            688
          ]
        }
      ]
    }
  ],
  "modules": [
    {
      "abstract_name": "matrix",
      "bbox": [
        0,
        0,
        2480,
        3528
      ],
      "concrete_name": "matrix_0",
      "constraints": [
        {
          "abut": false,
          "constraint": "order",
          "direction": "top_to_bottom",
          "instances": [
            "u0",
            "u1",
            "u2",
            "u3"
          ]
        },
        {
          "constraint": "same_template",
          "instances": [
            "u0",
            "u1",
            "u2",
            "u3"
          ]
        }
      ],
      "instances": [
        {
          "abstract_template_name": "row",
          "concrete_template_name": "row_0",
          "fa_map": [
            {
              "actual": "inp",
              "formal": "inp"
            },
            {
              "actual": "x1",
              "formal": "out"
            }
          ],
          "instance_name": "u0",
          "transformation": {
            "oX": 0,
            "oY": 2688,
            "sX": 1,
            "sY": 1
          }
        },
        {
          "abstract_template_name": "row",
          "concrete_template_name": "row_0",
          "fa_map": [
            {
              "actual": "x1",
              "formal": "inp"
            },
            {
              "actual": "x2",
              "formal": "out"
            }
          ],
          "instance_name": "u1",
          "transformation": {
            "oX": 0,
            "oY": 1764,
            "sX": 1,
            "sY": 1
          }
        },
        {
          "abstract_template_name": "row",
          "concrete_template_name": "row_0",
          "fa_map": [
            {
              "actual": "x2",
              "formal": "inp"
            },
            {
              "actual": "x3",
              "formal": "out"
            }
          ],
          "instance_name": "u2",
          "transformation": {
            "oX": 0,
            "oY": 924,
            "sX": 1,
            "sY": 1
          }
        },
        {
          "abstract_template_name": "row",
          "concrete_template_name": "row_0",
          "fa_map": [
            {
              "actual": "x3",
              "formal": "inp"
            },
            {
              "actual": "out",
              "formal": "out"
            }
          ],
          "instance_name": "u3",
          "transformation": {
            "oX": 0,
            "oY": 0,
            "sX": 1,
            "sY": 1
          }
        }
      ],
      "parameters": [
        "inp",
        "out"
      ]
    },
    {
      "abstract_name": "row",
      "bbox": [
        0,
        0,
        2480,
        840
      ],
      "concrete_name": "row_0",
      "constraints": [
        {
          "abut": false,
          "constraint": "order",
          "direction": "left_to_right",
          "instances": [
            "u0",
            "u1",
            "u2"
          ]
        },
        {
          "constraint": "same_template",
          "instances": [
            "u0",
            "u1",
            "u2"
          ]
        }
      ],
      "instances": [
        {
          "abstract_template_name": "slice",
          "concrete_template_name": "slice_a",
          "fa_map": [
            {
              "actual": "inp",
              "formal": "inp"
            },
            {
              "actual": "x1",
              "formal": "out"
            }
          ],
          "instance_name": "u0",
          "transformation": {
            "oX": 0,
            "oY": 0,
            "sX": 1,
            "sY": 1
          }
        },
        {
          "abstract_template_name": "slice",
          "concrete_template_name": "slice_a",
          "fa_map": [
            {
              "actual": "x1",
              "formal": "inp"
            },
            {
              "actual": "x2",
              "formal": "out"
            }
          ],
          "instance_name": "u1",
          "transformation": {
            "oX": 880,
            "oY": 0,
            "sX": 1,
            "sY": 1
          }
        },
        {
          "abstract_template_name": "slice",
          "concrete_template_name": "slice_a",
          "fa_map": [
            {
              "actual": "x2",
              "formal": "inp"
            },
            {
              "actual": "out",
              "formal": "out"
            }
          ],
          "instance_name": "u2",
          "transformation": {
            "oX": 1680,
            "oY": 0,
            "sX": 1,
            "sY": 1
          }
        }
      ],
      "parameters": [
        "inp",
        "out"
      ]
    }
  ]
}
"""

    placement_verilog_d = json.loads(txt)


    cn = 'matrix_0'
    nets_d = gen_netlist( placement_verilog_d, cn)

    assert 27584 == calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)

    placement_verilog_d['modules'][1]['instances'][1]['transformation']["oY"] += 840
    placement_verilog_d['modules'][1]['instances'][1]['transformation']["sY"] = -1

    assert standalone_overlap_checker( placement_verilog_d, cn)

    hpwl = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)
    print(hpwl)
    assert 27584 > hpwl

    placement_verilog_d['modules'][0]['instances'][1]['transformation']["oX"] += 2480
    placement_verilog_d['modules'][0]['instances'][1]['transformation']["sX"] = -1
    assert standalone_overlap_checker( placement_verilog_d, cn)

    hpwl2 = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)
    print(hpwl2)
    assert hpwl > hpwl2

    placement_verilog_d['modules'][0]['instances'][3]['transformation']["oX"] += 2480
    placement_verilog_d['modules'][0]['instances'][3]['transformation']["sX"] = -1
    assert standalone_overlap_checker( placement_verilog_d, cn)

    hpwl3 = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)
    print(hpwl3)
    assert hpwl2 > hpwl3

    placement_verilog_d['modules'][0]['instances'][0]['transformation']["oY"] += 840
    placement_verilog_d['modules'][0]['instances'][0]['transformation']["sY"] = -1
    placement_verilog_d['modules'][0]['instances'][1]['transformation']["oY"] += 840
    placement_verilog_d['modules'][0]['instances'][1]['transformation']["sY"] = -1
    placement_verilog_d['modules'][0]['instances'][2]['transformation']["oY"] += 840
    placement_verilog_d['modules'][0]['instances'][2]['transformation']["sY"] = -1
    placement_verilog_d['modules'][0]['instances'][3]['transformation']["oY"] += 840
    placement_verilog_d['modules'][0]['instances'][3]['transformation']["sY"] = -1
    assert standalone_overlap_checker( placement_verilog_d, cn)

    hpwl4 = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)
    print(hpwl4)
    assert hpwl3 > hpwl4

    placement_verilog_d['modules'][1]['instances'][1]['transformation']["oX"] -= 80
    placement_verilog_d['modules'][1]['instances'][2]['transformation']["oX"] -= 80
    assert standalone_overlap_checker( placement_verilog_d, cn)

    hpwl5 = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)
    print(hpwl5)
    assert hpwl4 > hpwl5

    placement_verilog_d['modules'][0]['instances'][0]['transformation']["oY"] -= 2*84
    placement_verilog_d['modules'][0]['instances'][1]['transformation']["oY"] -= 84
    placement_verilog_d['modules'][0]['instances'][2]['transformation']["oY"] -= 84

    placement_verilog_d['modules'][0]['instances'][1]['transformation']["oX"] -= 80
    placement_verilog_d['modules'][0]['instances'][3]['transformation']["oX"] -= 80

    assert standalone_overlap_checker( placement_verilog_d, cn)

    hpwl6 = calculate_HPWL_from_placement_verilog_d( placement_verilog_d, cn, nets_d)
    print(hpwl6)
    assert hpwl5 > hpwl6

    print( hpwl6 / 27584 - 1)

    placement_verilog_d['modules'][0]['concrete_name'] = 'matrix_ref'
    placement_verilog_d['modules'][0]['bbox'][2] -= 80
    placement_verilog_d['modules'][0]['bbox'][3] -= 2*84
    placement_verilog_d['modules'][1]['bbox'][2] -= 80

    with pathlib.Path( '__reference_placement_verilog_d__').open('wt') as fp:
        json.dump( placement_verilog_d, fp=fp, indent=2)
