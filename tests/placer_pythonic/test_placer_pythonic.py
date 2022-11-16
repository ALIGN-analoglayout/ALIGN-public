import pytest
import json
import plotly.graph_objects as go
import plotly.express as px

from align.pnr.placer_pythonic import pythonic_placer, propagate_down_global_signals, trim_placement_data
from align.cell_fabric.transformation import Transformation, Rect

DISABLE_TESTS = True


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
                'terminals': [
                    {'layer': 'M1', 'netName': 'D', 'rect': [2000, 1000, 2500, 11000], 'netType': 'pin'},
                    {'layer': 'M1', 'netName': 'G', 'rect': [3000, 1000, 3500, 11000], 'netType': 'pin'},
                    {'layer': 'M1', 'netName': 'S', 'rect': [4000, 1000, 4500, 110000], 'netType': 'pin'}
                ],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'NMOS_3T',
                'concrete_template_name': 'NMOS_3T_X2_Y1',
                'bbox': [0, 0, 10800, 6300],
                'terminals': [
                    {'layer': 'M2', 'netName': 'D', 'rect': [1000, 1000, 9000, 1500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'G', 'rect': [1000, 3000, 9000, 3500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'S', 'rect': [1000, 5000, 9000, 5500], 'netType': 'pin'}
                ],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'PMOS_3T',
                'concrete_template_name': 'PMOS_3T_X1_Y2',
                'bbox': [0, 0, 6480, 12600],
                'terminals': [
                    {'layer': 'M1', 'netName': 'D', 'rect': [2000, 1000, 2500, 10000], 'netType': 'pin'},
                    {'layer': 'M1', 'netName': 'G', 'rect': [3000, 1000, 3500, 10000], 'netType': 'pin'},
                    {'layer': 'M1', 'netName': 'S', 'rect': [4000, 1000, 4500, 10000], 'netType': 'pin'}
                ],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'PMOS_3T',
                'concrete_template_name': 'PMOS_3T_X2_Y1',
                'bbox': [0, 0, 10800, 6300],
                'terminals': [
                    {'layer': 'M2', 'netName': 'D', 'rect': [1000, 1000, 9000, 1500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'G', 'rect': [1000, 3000, 9000, 3500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'S', 'rect': [1000, 5000, 9000, 5500], 'netType': 'pin'}
                ],
                'constraints': place_on_grid
            }
        ],
        'modules': [
            {
                'name': 'ring_oscillator_stage',
                'parameters': ['VI', 'VO', 'VCC', 'VSSX'],
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
                        'fa_map': [{'formal': 'D', 'actual': 'VO'}, {'formal': 'G', 'actual': 'VI'}, {'formal': 'S', 'actual': 'VCC'}]
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
                        'fa_map': [{'formal': 'VCC', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'VO'}, {'formal': 'VO', 'actual': 'V1'}]
                    },
                    {
                        'instance_name': 'XI2', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCC', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V1'}, {'formal': 'VO', 'actual': 'V2'}]
                    },
                    {
                        'instance_name': 'XI3', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCC', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V2'}, {'formal': 'VO', 'actual': 'V3'}]
                    },
                    {
                        'instance_name': 'XI4', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCC', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V3'}, {'formal': 'VO', 'actual': 'V4'}]
                    },
                    {
                        'instance_name': 'XI5', 'abstract_template_name': 'ring_oscillator_stage',
                        'fa_map': [{'formal': 'VCC', 'actual': 'VCCX'}, {'formal': 'VSSX', 'actual': 'VSSX'},
                                   {'formal': 'VI', 'actual': 'V4'}, {'formal': 'VO', 'actual': 'VO'}]
                    }
                ]
            }
        ],
        'global_signals': [
            {
                "prefix": "global_power",
                "formal": "supply0",
                "actual": "VSSX"
            },
            {
                "prefix": "global_power",
                "formal": "supply1",
                "actual": "VCCX"
            }
        ]
    }
    return data


def ota():
    place_on_grid = [
        {'constraint': 'PlaceOnGrid', 'direction': 'H', 'pitch': 12600, 'ored_terms': [{'offsets': [0], 'scalings': [1, -1]}]},
        {'constraint': 'PlaceOnGrid', 'direction': 'V', 'pitch': 1080, 'ored_terms': [{'offsets': [0], 'scalings': [1, -1]}]}
    ]
    data = {
        'leaves': [
            {
                'abstract_template_name': 'NMOS_3T',
                'concrete_template_name': 'NMOS_3T_X2_Y1',
                'bbox': [0, 0, 10800, 6300],
                'terminals': [
                    {'layer': 'M2', 'netName': 'D', 'rect': [1000, 1000, 9000, 1500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'G', 'rect': [1000, 3000, 9000, 3500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'S', 'rect': [1000, 5000, 9000, 5500], 'netType': 'pin'}
                ],
                'constraints': place_on_grid
            },
            {
                'abstract_template_name': 'PMOS_3T',
                'concrete_template_name': 'PMOS_3T_X2_Y1',
                'bbox': [0, 0, 10800, 6300],
                'terminals': [
                    {'layer': 'M2', 'netName': 'D', 'rect': [1000, 1000, 9000, 1500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'G', 'rect': [1000, 3000, 9000, 3500], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': 'S', 'rect': [1000, 5000, 9000, 5500], 'netType': 'pin'}
                ],
                'constraints': place_on_grid
            }
        ],
        'modules': [
            {
                'name': 'ota',
                'parameters': ['VBIAS', 'VIN', 'VIP', 'VOP', 'VCCX', 'VSSX'],
                'constraints': [],
                'instances': [
                    {
                        'instance_name': 'XI0', 'abstract_template_name': 'NMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VCM'}, {'formal': 'G', 'actual': 'VBIAS'}, {'formal': 'S', 'actual': 'VSSX'}]
                    },
                    {
                        'instance_name': 'XI1', 'abstract_template_name': 'NMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VON'}, {'formal': 'G', 'actual': 'VIP'}, {'formal': 'S', 'actual': 'VCM'}]
                    },
                    {
                        'instance_name': 'XI2', 'abstract_template_name': 'NMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VOP'}, {'formal': 'G', 'actual': 'VIN'}, {'formal': 'S', 'actual': 'VCM'}]
                    },
                    {
                        'instance_name': 'XI3', 'abstract_template_name': 'PMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VON'}, {'formal': 'G', 'actual': 'VON'}, {'formal': 'S', 'actual': 'VCCX'}]
                    },
                    {
                        'instance_name': 'XI4', 'abstract_template_name': 'PMOS_3T',
                        'fa_map': [{'formal': 'D', 'actual': 'VOP'}, {'formal': 'G', 'actual': 'VON'}, {'formal': 'S', 'actual': 'VCCX'}]
                    }
                ]
            }
        ],
        'global_signals': [
            {
                "prefix": "global_power",
                "formal": "supply0",
                "actual": "VSSX"
            },
            {
                "prefix": "global_power",
                "formal": "supply1",
                "actual": "VCCX"
            }
        ]
    }
    return data


DRAW = False


def draw_placement(placement_data, module_name):
    if not DRAW:
        return

    leaves = {x['concrete_name']: x for x in placement_data['leaves']}
    modules = {x['concrete_name']: x for x in placement_data['modules']}
    module = modules[module_name]

    colorscale = px.colors.qualitative.Alphabet

    fig = go.Figure()
    fig.update_xaxes(range=[0, max(module['bbox'])])
    fig.update_yaxes(range=[0, max(module['bbox'])])

    # Add shapes
    x_lst = list()
    y_lst = list()
    n_lst = list()

    i = 0
    for instance in module['instances']:
        concrete_name = instance['concrete_template_name']

        if concrete_name in leaves:
            bbox = leaves[concrete_name]['bbox']
        elif concrete_name in modules:
            bbox = modules[concrete_name]['bbox']
        else:
            assert False

        bbox = Transformation(
            instance['transformation']['oX'],
            instance['transformation']['oY'],
            instance['transformation']['sX'],
            instance['transformation']['sY']
            ).hitRect(Rect(*bbox)).canonical().toList()

        llx, lly, urx, ury = bbox

        color = colorscale[i % len(colorscale)]
        fig.add_shape(type="rect", x0=llx, y0=lly, x1=urx, y1=ury, line=dict(color="RoyalBlue", width=3), fillcolor=color)
        i += 1
        x_lst.append((llx+urx)/2)
        y_lst.append((lly+ury)/2)
        n_lst.append(f"{instance['instance_name']}")

    fig.update_shapes(opacity=0.5, xref="x", yref="y")

    # Add labels
    fig.add_trace(go.Scatter(x=x_lst, y=y_lst, text=n_lst, mode="text", textfont=dict(color="black", size=24)))

    fig.show()


@pytest.mark.skipif(not DISABLE_TESTS, "Disabled using global variable")
def test_place_ring_oscillator():
    input_data = ring_oscillator()
    with open('placement_input.json', "wt") as fp:
        fp.write(json.dumps(input_data, indent=2) + '\n')
    placement_data = pythonic_placer('ring_oscillator', input_data)
    placement_data = trim_placement_data(placement_data, 'ring_oscillator')
    assert len(placement_data['leaves']) == 2
    assert len(placement_data['modules']) == 2
    with open('placement_output.json', "wt") as fp:
        json.dump(placement_data, fp=fp, indent=2)
    draw_placement(placement_data, 'ring_oscillator_0')


@pytest.mark.skipif(not DISABLE_TESTS, "Disabled using global variable")
def test_place_ring_oscillator_stage():
    input_data = ring_oscillator()
    placement_data = pythonic_placer('ring_oscillator_stage', input_data)
    assert len(placement_data['leaves']) == 2
    assert len(placement_data['modules']) == 1
    draw_placement(placement_data, 'ring_oscillator_stage_0')


@pytest.mark.skipif(not DISABLE_TESTS, "Disabled using global variable")
def test_place_spread():  # Test relies on ALIGN's constraint checker
    input_data = ring_oscillator()
    modules = {module['name']: module for module in input_data['modules']}
    modules['ring_oscillator_stage']['constraints'].append({
        'constraint': 'Spread',
        'direction': 'vertical',
        'distance': 100,
        'instances': [i['instance_name'] for i in modules['ring_oscillator_stage']['instances']]
        })
    placement_data = pythonic_placer('ring_oscillator_stage', input_data, scale_factor=10)
    draw_placement(placement_data, 'ring_oscillator_stage_0')


@pytest.mark.skipif(not DISABLE_TESTS, "Disabled using global variable")
def test_place_floorplan():  # Test relies on ALIGN's constraint checker
    input_data = ota()
    modules = {module['name']: module for module in input_data['modules']}
    modules['ota']['constraints'].append({
        'constraint': 'Floorplan',
        'order': True,
        'symmetrize': True,
        'regions': [['XI3', 'XI4'], ['XI1', 'XI2'], ['XI0']]
        })
    placement_data = pythonic_placer('ota', input_data, scale_factor=10)
    draw_placement(placement_data, 'ota_0')


@pytest.mark.skipif(not DISABLE_TESTS, "Disabled using global variable")
def test_propagate_down_global_signals():
    input_data = ring_oscillator()
    modules = {module['name']: module for module in input_data['modules']}
    global_signals = [x['actual'] for x in input_data['global_signals']]
    propagate_down_global_signals(modules, 'ring_oscillator', global_signals)
    assert set(modules['ring_oscillator_stage']['global_signals']) == {'VCC', 'VSSX'}


# TODO: compute_topoorder
# TODO: trim_placement_data
