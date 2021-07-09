import re

# SY: Syntax converter


def convert_align_to_adr(term):
    """ Convert align terminal to adr terminal (M -> colored metal, V -> colored via, netName -> net_name"""
    assert 'netName' in term, term
    new_term = dict()
    new_term['net_name'] = term['netName']
    new_term['rect'] = term['rect'].copy()
    prefix = 'metal' if term['layer'][0] == 'M' else 'via'
    if 'color' in term and term['color'] is not None:
        color = term['color']
    else:
        color = ''
    new_term['layer'] = prefix + color + term['layer'][1:]
    if 'width' in term:
        new_term['width'] = term['width']
    if 'connected_pins' in term:
        new_term['connected_pins'] = term['connected_pins'].copy()
    return new_term

# SY: Added for coloring


def extract_layer_color(layer):
    """ Returns layer and color from colored layer. Example: viaa1 => via1, a"""
    mg = re.match(r'(metal|via)(\D+)(\d+)', layer)
    if mg:
        lyr = mg.group(1) + mg.group(3)
        clr = mg.group(2)
    else:
        lyr = layer
        clr = None
    return lyr, clr

# SY: Added for coloring


def translate_layer(layer):
    """ Translates metal/via to M/V"""
    metal_layer_map = {f'metal{i}': f'M{i}' for i in range(0, 7)}
    via_layer_map = {f'via{i}': f'V{i}' for i in range(0, 6)}
    layer_map = dict(list(metal_layer_map.items()) + list(via_layer_map.items()))
    return layer_map.get(layer, layer)
