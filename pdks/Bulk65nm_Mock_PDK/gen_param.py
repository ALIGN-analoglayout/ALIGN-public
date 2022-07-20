import json
import logging
from math import sqrt, floor, ceil, log10
from copy import deepcopy
from collections import Counter

logger = logging.getLogger(__name__)


def limit_pairs(pairs):
    # Hack to limit aspect ratios when there are a lot of choices
    if len(pairs) > 12:
        new_pairs = []
        log10_aspect_ratios = [-0.3, 0, 0.3]
        for l in log10_aspect_ratios:
            best_pair = min((abs(log10(newy) - log10(newx) - l), (newx, newy))
                            for newx, newy in pairs)[1]
            new_pairs.append(best_pair)
        return new_pairs
    else:
        return pairs

def construct_sizes_from_exact_patterns(exact_patterns):

    legal_size_d = {}

    for pattern in exact_patterns:
        histo = Counter(c for row in pattern for c in row)
        num_devices = len(set(c.upper() for c in histo.keys()))
        if num_devices == 2:
            k = len(pattern[0])//2, len(pattern)
        else:
            k = len(pattern[0]), len(pattern)
        assert k not in legal_size_d
        legal_size_d[k] = pattern

    return legal_size_d

def check_legal(x, y, legal_sizes):
    assert legal_sizes is not None
    for d in legal_sizes:
        for tag, val in [('x', x), ('y', y)]:
            if tag in d and d[tag] != val:
                break
        else:
            return True

    return False

def add_primitive(primitives, block_name, block_args, generator_constraint):

    if block_name in primitives:
        block_args['abstract_template_name'] = block_name
        block_args['concrete_template_name'] = block_name
        if not primitives[block_name] == block_args:
            logger.warning(f"Distinct devices mapped to the same primitive {block_name}: \
                             existing: {primitives[block_name]}\
                             new: {block_args}")
    else:
        logger.debug(f"Found primitive {block_name} with {block_args}")
        if 'x_cells' in block_args and 'y_cells' in block_args:
            x, y = block_args['x_cells'], block_args['y_cells']
            pairs = set()
            m = x*y
            y_sqrt = floor(sqrt(x*y))
            for y in range(y_sqrt, 0, -1):
                if m % y == 0:
                    pairs.add((y, m//y))
                    pairs.add((m//y, y))
                if y == 1:
                    break

            legal_size_set = None
            legal_sizes = None
            if generator_constraint is not None:
                generator_parameters = generator_constraint.parameters
                if generator_parameters is not None:
                    legal_sizes = generator_parameters.get('legal_sizes')
                    exact_patterns = generator_parameters.get('exact_patterns')
                    assert exact_patterns is None or legal_sizes is None
                    if exact_patterns is not None:
                        legal_size_set = set(construct_sizes_from_exact_patterns(exact_patterns).keys())

            if legal_size_set is None and legal_sizes is None:
                pairs = limit_pairs((pairs)) # call limit_pairs if there aren't constraints

            for newx, newy in pairs:
                if legal_sizes is not None: # legal_sizes
                    ok = check_legal(newx, newy, legal_sizes)
                else:
                    ok = legal_size_set is None or (newx, newy) in legal_size_set

                if legal_sizes is not None or legal_size_set is not None:
                    if ok:
                        logger.debug(f"Adding matching primitive of size {newx} {newy} {generator_constraint}")
                    else:
                        logger.debug(f"Not adding primitive of size {newx} {newy} because it doesn't match {generator_constraint}")

                if ok:
                    concrete_name = f'{block_name}_X{newx}_Y{newy}'
                    if concrete_name not in primitives:
                        primitives[concrete_name] = deepcopy(block_args)
                        primitives[concrete_name]['x_cells'] = newx
                        primitives[concrete_name]['y_cells'] = newy
                        primitives[concrete_name]['abstract_template_name'] = block_name
                        primitives[concrete_name]['concrete_template_name'] = concrete_name
        else:
            primitives[block_name] = block_args
            primitives[block_name]['abstract_template_name'] = block_name
            primitives[block_name]['concrete_template_name'] = block_name

def gen_param(subckt, primitives, pdk_dir):

    generator_constraint = None
    for const in subckt.constraints:
        if const.constraint == 'Generator':
            assert generator_constraint is None
            generator_constraint = const

    block_name = subckt.name
    vt = subckt.elements[0].model
    values = subckt.elements[0].parameters
    generator_name = subckt.generator["name"]
    block_name = subckt.name
    logger.debug(f"Getting generator parameters for: {subckt.name}")
    generator_name = subckt.generator["name"]
    layers_json = pdk_dir / "layers.json"
    with open(layers_json, "rt") as fp:
        pdk_data = json.load(fp)
    design_config = pdk_data["design_info"]

    if len(subckt.elements) == 1:
        values = subckt.elements[0].parameters
    else:
        mvalues = {}
        for ele in subckt.elements:
            mvalues[ele.name] = ele.parameters

    if generator_name == 'CAP':

        size = round(float(values["VALUE"]) * 1E15, 4)

        assert size <= design_config["max_size_cap"], f"caps larger than {design_config['max_size_cap']}fF are not supported"

        if "L" in values and "W" in values:
            length = round(float(values["L"]) * 1E9, 4)
            width = round(float(values["W"]) * 1E9, 4)
        else:
            # HACK for unit cap used in common centroid and support older SPICE
            length = int((sqrt(size/2))*1000)
            width = int((sqrt(size/2))*1000)

        # TODO: use float in name
        logger.debug(f"Generating capacitor for:{block_name}, {size}")
        block_args = {
            'primitive': generator_name,
            'value':  [int(length), int(width)]
        }
        add_primitive(primitives, block_name, block_args, generator_constraint)

    elif generator_name == 'RES':
        assert float(values["VALUE"]) or float(values["R"]), f"unidentified size {values['VALUE']} for {block_name}"
        if "R" in values:
            size = round(float(values["R"]), 2)
        elif 'VALUE' in values:
            size = round(float(values["VALUE"]), 2)
        # TODO: use float in name
        if size.is_integer():
            size = int(size)
        height = ceil(sqrt(float(size) / design_config["unit_height_res"]))
        logger.debug(f'Generating resistor for: {block_name} {size}')
        block_args = {
            'primitive': generator_name,
            'value': (height, float(size))
        }
        add_primitive(primitives, block_name, block_args, generator_constraint)

    else:
        assert 'MOS' == generator_name, f'{generator_name} is not recognized'
        if "vt_type" in design_config:
            vt = [vt.upper() for vt in design_config["vt_type"] if vt.upper() in subckt.elements[0].model]
        mvalues = {}
        for ele in subckt.elements:
            mvalues[ele.name] = ele.parameters
        device_name_all = [*mvalues.keys()]
        device_name = next(iter(mvalues))

        for key in mvalues:
            assert mvalues[key]["W"] != str, f"unrecognized size of device {key}:{mvalues[key]['W']} in {block_name}"
            width = int(float(mvalues[key]["W"])*1E+9/design_config["Fin_pitch"])
        name_arg = 'W'+str(width)

        if 'NF' in mvalues[device_name].keys():
            for key in mvalues:
                assert int(mvalues[key]["NF"]), f"unrecognized NF of device {key}:{mvalues[key]['NF']} in {block_name}"
                assert int(mvalues[key]["NF"]) % 2 == 0, f"NF must be even for device {key}:{mvalues[key]['NF']} in {block_name}"
            name_arg = name_arg+'_NF'+str(int(mvalues[device_name]["NF"]))

        if 'M' in mvalues[device_name].keys():
            for key in mvalues:
                assert int(mvalues[key]["M"]), f"unrecognized M of device {key}:{mvalues[key]['M']} in {block_name}"
                if "PARALLEL" in mvalues[key].keys() and int(mvalues[key]['PARALLEL']) > 1:
                    mvalues[key]["PARALLEL"] = int(mvalues[key]['PARALLEL'])
                    mvalues[key]['M'] = int(mvalues[key]['M'])*int(mvalues[key]['PARALLEL'])
            name_arg = name_arg+'_M'+str(int(mvalues[device_name]["M"]))
            size = 0

        logger.debug(f"Generating lef for {block_name}")

        if isinstance(size, int):
            for key in mvalues:
                assert int(float(mvalues[device_name]["W"])*1E+9) == int(float(mvalues[key]["W"])*1E+9), f"W should be same for all devices in {block_name} {mvalues}"
                size_device = int(mvalues[key]["NF"])*int(mvalues[key]["M"])
                size = size + size_device
            no_units = ceil(size / (2*len(mvalues)))  # Factor 2 is due to NF=2 in each unit cell; needs to be generalized
            square_y = floor(sqrt(no_units))
            while no_units % square_y != 0:
                square_y -= 1
            yval = square_y
            xval = int(no_units / square_y)
        def total_device_size(v):
            return int(float(v["W"])*1E+9)*int(v['NF'])*int(v["M"])
        unequal_devices = None
        if len(device_name_all) == 2:
            unequal_devices = (total_device_size(mvalues[device_name_all[0]]) !=
                               total_device_size(mvalues[device_name_all[1]]))
        if unequal_devices:
            yval = 1
            xval = int(no_units)

        if generator_constraint is not None:
                generator_parameters = generator_constraint.parameters
                if generator_parameters is not None:
                    exact_patterns = generator_parameters.get('exact_patterns')
                    if exact_patterns is not None:
                        yval = len(exact_patterns[0])
                        xval = len(exact_patterns[0][0]) if len(device_name_all) !=2 else len(exact_patterns[0][0])//2

        block_args = {
            'primitive': generator_name,
            'value': width,
            'x_cells': xval,
            'y_cells': yval,
            'parameters': mvalues
        }
        if 'STACK' in mvalues[device_name].keys() and int(mvalues[device_name]["STACK"]) > 1:
            block_args['stack'] = int(mvalues[device_name]["STACK"])
        if vt:
            block_args['vt_type'] = vt[0]
        # TODO: remove name based hack
        if 'SCM' in block_name and unequal_devices:
            primitives[block_name] = block_args
            primitives[block_name]['abstract_template_name'] = block_name
            primitives[block_name]['concrete_template_name'] = block_name
        else:
            add_primitive(primitives, block_name, block_args, generator_constraint)
    return True
