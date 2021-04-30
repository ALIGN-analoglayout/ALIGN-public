
from align.pnr.render_placement import dump_blocks2


def test_dump_blocks2():
    placement_verilog_d = {
        "modules": [
            { "name": "top",
              "bbox": [0,0,100,100],
              "parameters": [],
              "instances": [
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u0",
                      "transformation": { "oX": 0, "oY": 0, "sX": 1, "sY": 1}
                  },
                  {
                      "abstract_template_name": "a",
                      "concrete_template_name": "a",
                      "instance_name": "u1",
                      "transformation": { "oX": 0, "oY": 20, "sX": 1, "sY": 1}
                  }
              ]
              
            }
        ],
        "leaves": [
            { "name": "a",
              "bbox": [0,0,10,10]
            }
        ]
    }
    
    dump_blocks2( placement_verilog_d, 'top', 0, show=False)
