from align.pnr.render_placement import gen_boxes_and_hovertext

def test_gen_boxes_and_hovertext():
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
    
    lst = list(gen_boxes_and_hovertext( placement_verilog_d, 'top'))
    bbox_rects = [ tup[0] for tup in lst if tup[2] and not tup[4]]
    term_rects = [ tup[0] for tup in lst if tup[2] and tup[4]]

    assert bbox_rects[0] == [0,0,10,10]
    assert bbox_rects[1] == [0,20,10,30]

    assert term_rects[0] == [4,4,6,6]
    assert term_rects[1] == [4,24,6,26]


