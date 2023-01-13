import json
import pathlib

from align.schema.hacks import VerilogJsonTop
from align.pnr.checker import check_placement
from align.pnr.placer_pythonic_sp import place_using_sequence_pairs


def compute_topoorder(modules, concrete_name, key='abstract_template_name'):
    found_modules, found_leaves = set(), set()
    order = list()

    def aux(cn):
        if cn in modules:
            found_modules.add(cn)
            for instance in modules[cn]['instances']:
                ctn = instance[key]
                if ctn not in found_modules and ctn not in found_leaves:
                    aux(ctn)
            order.append(cn)
        else:
            found_leaves.add(cn)
            order.append(cn)
    aux(concrete_name)

    return order, found_modules, found_leaves


def trim_placement_data(placement_data, top_level):

    modules = {module['concrete_name']: module for module in placement_data['modules']}

    top_concrete_names = [module['concrete_name'] for module in placement_data['modules'] if module['abstract_name'] == top_level]
    all_modules_leaves = set()
    for concrete_name in top_concrete_names:
        _, found_modules, found_leaves = compute_topoorder(modules, concrete_name, key='concrete_template_name')
        all_modules_leaves.update(found_modules)
        all_modules_leaves.update(found_leaves)

    new_placement_data = {'leaves': list(), 'modules': list()}
    for key in ['leaves', 'modules']:
        new_placement_data[key] = [x for x in placement_data[key] if x['concrete_name'] in all_modules_leaves]
        for elem in new_placement_data[key]:
            if 'pin_bbox' in elem:
                del elem['pin_bbox']
            if 'global_signals' in elem:
                elem['global_signals'] = list(elem['global_signals'])

    return new_placement_data


def propagate_down_global_signals(modules: dict, module_name: str, global_signals: set):
    GS = 'global_signals'
    if GS in modules[module_name]:
        modules[module_name][GS].update(global_signals)
    else:
        modules[module_name][GS] = set(global_signals)
    for instance in modules[module_name]['instances']:
        sub_module_name = instance['abstract_template_name']
        if sub_module_name in modules:
            signals_to_propagate = set()
            for formal_actual in instance['fa_map']:
                formal = formal_actual['formal']
                actual = formal_actual['actual']
                if actual in global_signals and formal not in modules[sub_module_name].get(GS, set()):
                    signals_to_propagate.add(formal)
            if signals_to_propagate:
                propagate_down_global_signals(modules, sub_module_name, signals_to_propagate)


def pythonic_placer(top_level, input_data, scale_factor=1):

    placement_data = dict()
    placement_data['modules'] = list()
    placement_data['leaves'] = list()
    placement_data['scale_factor'] = scale_factor
    for leaf in input_data['leaves']:
        # Calculate a bounding box for each pin for HPWL calculation
        pin_bbox = dict()
        for term in leaf['terminals']:
            if term['netType'] == 'pin':
                net_name = term['netName']
                if net_name not in pin_bbox:
                    pin_bbox[net_name] = [x for x in term['rect']]
                else:
                    pin_bbox[net_name][0] = min(pin_bbox[net_name][0], term['rect'][0])
                    pin_bbox[net_name][1] = min(pin_bbox[net_name][1], term['rect'][1])
                    pin_bbox[net_name][2] = max(pin_bbox[net_name][2], term['rect'][2])
                    pin_bbox[net_name][3] = max(pin_bbox[net_name][3], term['rect'][3])

        placement_data['leaves'].append({
            'abstract_name': leaf['abstract_template_name'],
            'concrete_name': leaf['concrete_template_name'],
            'constraints': leaf['constraints'],
            'bbox': leaf['bbox'],
            'terminals': leaf['terminals'],
            'pin_bbox': pin_bbox})

    modules = {module['name']: module for module in input_data['modules']}
    topological_order, found_modules, _ = compute_topoorder(modules, top_level)

    # Propagate power pins down the modules
    if global_signals := {x['actual'] for x in input_data['global_signals']}:
        propagate_down_global_signals(modules, top_level, global_signals)

    for name in topological_order:
        if name not in found_modules:
            continue

        # Select and call placement algorithm here
        place_using_sequence_pairs(placement_data, modules[name], top_level)

    check_placement(VerilogJsonTop.parse_obj(placement_data), scale_factor)

    # Trim unused modules and leaves
    placement_data = trim_placement_data(placement_data, top_level)

    return placement_data


def pythonic_placer_driver(top_level, input_dir: pathlib.Path, scale_factor=1):

    with (input_dir / f'{top_level}.verilog.json').open('rt') as fp:
        input_data = json.load(fp)

    input_data['leaves'] = list()

    modules = {module['name']: module for module in input_data['modules']}
    _, _, found_leaves = compute_topoorder(modules, top_level)

    for abstract_template_name in found_leaves:
        json_files = input_dir.glob(f'{abstract_template_name}*.json')
        for filename in json_files:
            if not filename.name.endswith('gds.json'):
                with (input_dir / filename).open('rt') as fp:
                    leaf_data = json.load(fp)
                    del leaf_data['globalRoutes']
                    del leaf_data['globalRouteGrid']
                    assert 'bbox' in leaf_data
                    assert 'terminals' in leaf_data
                    leaf_data['abstract_template_name'] = abstract_template_name
                    leaf_data['concrete_template_name'] = filename.stem
                    leaf_data['constraints'] = list()
                    # TODO: Append PlaceOnGrid if exists
                    input_data['leaves'].append(leaf_data)

    placement_data = pythonic_placer(top_level, input_data, scale_factor=scale_factor)
    return placement_data
