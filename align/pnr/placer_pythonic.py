import logging

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
    all_modules_leaves = list()
    for concrete_name in top_concrete_names:
        _, found_modules, found_leaves = compute_topoorder(modules, concrete_name, key='concrete_template_name')
        all_modules_leaves.extend(found_modules)
        all_modules_leaves.extend(found_leaves)

    all_modules_leaves = set(all_modules_leaves)

    new_placement_data = {'leaves': list(), 'modules': list()}
    new_placement_data['leaves'] = [leaf for leaf in placement_data['leaves'] if leaf['concrete_name'] in all_modules_leaves]
    new_placement_data['modules'] = [leaf for leaf in placement_data['modules'] if leaf['concrete_name'] in all_modules_leaves]

    for key in ['leaves', 'modules']:
        for elem in new_placement_data[key]:
            if 'pin_bbox' in elem:
                del elem['pin_bbox']

    return new_placement_data


def propagate_down_global_signals(modules: dict, module_name: str, global_signals: list):
    GS = 'global_signals'
    modules[module_name][GS] = modules[module_name].get(GS, list()) + global_signals
    for instance in modules[module_name]['instances']:
        sub_module_name = instance['abstract_template_name']
        if sub_module_name in modules:
            signals_to_propagate = list()
            for formal_actual in instance['fa_map']:
                formal = formal_actual['formal']
                actual = formal_actual['actual']
                if actual in global_signals and formal not in modules[sub_module_name].get(GS, list()):
                    signals_to_propagate.append(formal)
            if signals_to_propagate:
                propagate_down_global_signals(modules, sub_module_name, signals_to_propagate)


def pythonic_placer(top_level, input_data, scale_factor=1):

    placement_data = dict()
    placement_data['modules'] = list()
    placement_data['leaves'] = list()
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
    if global_signals := [x['actual'] for x in input_data['global_signals']]:
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
