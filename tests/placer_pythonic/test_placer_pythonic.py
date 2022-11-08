import json
from align.pnr.placer_pythonic import pythonic_placer


def ring_oscillator():
    place_on_grid = [
        {'constraint': 'PlaceOnGrid', 'direction': 'H', 'pitch': 12600, 'ored_terms': [{'offsets': [0], 'scalings': [1, -1]}]},
        {'constraint': 'PlaceOnGrid', 'direction': 'V', 'pitch': 1080, 'ored_terms': [{'offsets': [0], 'scalings': [1, -1]}]}
    ]
    data = {
        'leaves': [
            {
                'abstract_template_name': 'NMOS_3T',
                'concrete_template_name': 'NMOS_3T_X1_Y2',
                'bbox': [0, 0, 6480, 12600],
                'terminals': [],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'NMOS_3T',
                'concrete_template_name': 'NMOS_3T_X2_Y1',
                'bbox': [0, 0, 10800, 6300],
                'terminals': [],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'PMOS_3T',
                'concrete_template_name': 'PMOS_3T_X1_Y2',
                'bbox': [0, 0, 6480, 12600],
                'terminals': [],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'PMOS_3T',
                'concrete_template_name': 'PMOS_3T_X2_Y1',
                'bbox': [0, 0, 10800, 6300],
                'terminals': [],
                'constraints': place_on_grid
            }
        ],
        'modules': [
            {
                'name': 'ring_oscillator_stage',
                'parameters': ['VI', 'VO', 'VCCX', 'VSSX'],
                'constraints': [
                    {'constraint': 'Order', 'instances': ['X_MP0', 'X_MN0'], 'direction': 'top_to_bottom'}
                ],
                'instances': [
                    {
                        'instance_name': 'X_MN0', 'abstract_template_name': 'NMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VO'}, {'formal': 'G', 'actual': 'VI'}, {'formal': 'S', 'actual': 'VSSX'}]
                    },
                    {
                        'instance_name': 'X_MP0', 'abstract_template_name': 'PMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VO'}, {'formal': 'G', 'actual': 'VI'}, {'formal': 'S', 'actual': 'VCCX'}]
                    }
                    ]
            },
            {
                'name': 'ring_oscillator',
                'parameters': ['VO', 'VCCX', 'VSSX'],
                'constraints': [
                    {'constraint': 'Order', 'instances': ['XI1', 'XI2', 'XI3', 'XI4', 'XI5'], 'direction': 'left_to_right'},
                    {'constraint': 'SameTemplate', 'instances': ['XI1', 'XI2', 'XI3', 'XI4', 'XI5']}
                ],
                'instances': [
                    {
                        'instance_name': 'XI1', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCCX', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'VO'}, {'formal': 'VO', 'actual': 'V1'}]
                    },
                    {
                        'instance_name': 'XI2', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCCX', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V1'}, {'formal': 'VO', 'actual': 'V2'}]
                    },
                    {
                        'instance_name': 'XI3', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCCX', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V2'}, {'formal': 'VO', 'actual': 'V3'}]
                    },
                    {
                        'instance_name': 'XI4', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCCX', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V3'}, {'formal': 'VO', 'actual': 'V4'}]
                    },
                    {
                        'instance_name': 'XI5', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCCX', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V4'}, {'formal': 'VO', 'actual': 'VO'}]
                    }
                ]
            }
        ]
    }
    return data


def test_place_ring_oscillator():
    input_data = ring_oscillator()
    with open('placement_input.json', "wt") as fp:
        fp.write(json.dumps(input_data, indent=2) + '\n')
    placement_data = pythonic_placer('ring_oscillator', input_data)
    assert len(placement_data['leaves']) == 2
    assert len(placement_data['modules']) == 2
    with open('placement_output.json', "wt") as fp:
        json.dump(placement_data, fp=fp, indent=2)


def test_place_ring_oscillator_stage():
    input_data = ring_oscillator()
    placement_data = pythonic_placer('ring_oscillator_stage', input_data)
    assert len(placement_data['leaves']) == 2
    assert len(placement_data['modules']) == 1
