from align.pnr.render_placement import gen_boxes_and_hovertext

def test_gen_boxes_and_hovertext():
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
    
    lst = list(gen_boxes_and_hovertext( placement_verilog_d, 'top'))

    assert lst[0][0] == [0,0,10,10]
    assert lst[1][0] == [0,20,10,30]
