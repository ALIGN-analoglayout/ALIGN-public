from align.pnr.hpwl import gen_netlist, calculate_HPWL_from_placement_verilog_d

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
