from align.pnr.hpwl import gen_netlist

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
                      "fa_map": [
                          {
                              "formal": "x",
                              "actual": "y",
                          }
                      ]
                  },
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u1",
                      "transformation": { "oX": 0, "oY": 20, "sX": 1, "sY": 1},
                      "fa_map": [
                          {
                              "formal": "x",
                              "actual": "y",
                          }
                      ]
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

    assert nets_d[('y',)] == [ ('u0', 'x'), ('u1', 'x')]
