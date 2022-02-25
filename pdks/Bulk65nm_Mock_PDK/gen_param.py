import json
import logging
from math import sqrt, floor, ceil, log10
from copy import deepcopy
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

def add_primitive(primitives, block_name, block_args):
    if block_name in primitives:
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
                pairs = limit_pairs((pairs))
                for newx, newy in pairs:
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
    block_name = subckt.name
    vt = subckt.elements[0].model
    values = subckt.elements[0].parameters
    generator_name = subckt.generator["name"]
    block_name = subckt.name
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
        assert float(values["VALUE"]) or float(values["C"]), f"unidentified size {values} for {block_name}"
        if "C" in values:
            size = round(float(values["C"]) * 1E15, 4)
        elif 'VALUE' in values:
            size = round(float(values["VALUE"]) * 1E15, 4)
        assert size <= design_config["max_size_cap"], f"caps larger that {design_config['max_size_cap']}fF are not supported"

        # TODO: use float in name
        logger.debug(f"Generating capacitor for:{block_name}, {size}")
        block_args = {
            'primitive': generator_name,
            'value':  float(size)
        }
        add_primitive(primitives, block_name, block_args)

    elif generator_name == 'RES':
        assert float(values["VALUE"]) or float(values["R"]), f"unidentified size {values['VALUE']} for {name}"
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
        add_primitive(primitives, block_name, block_args)

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
            assert int(
                float(mvalues[key]["W"])*1E+9) % design_config["Fin_pitch"] == 0, \
                f"Width of device {key} in {block_name} should be multiple of fin pitch:{design_config['Fin_pitch']}"
            size = int(float(mvalues[key]["W"])*1E+9/design_config["Fin_pitch"])
            mvalues[key]["NFIN"] = size
        name_arg = 'NFIN'+str(size)

        if 'NF' in mvalues[device_name].keys():
            for key in mvalues:
                assert int(mvalues[key]["NF"]), f"unrecognized NF of device {key}:{mvalues[key]['NF']} in {name}"
                assert int(mvalues[key]["NF"]) % 2 == 0, f"NF must be even for device {key}:{mvalues[key]['NF']} in {name}"
            name_arg = name_arg+'_NF'+str(int(mvalues[device_name]["NF"]))

        if 'M' in mvalues[device_name].keys():
            for key in mvalues:
                assert int(mvalues[key]["M"]), f"unrecognized M of device {key}:{mvalues[key]['M']} in {name}"
                if "PARALLEL" in mvalues[key].keys() and int(mvalues[key]['PARALLEL']) > 1:
                    mvalues[key]["PARALLEL"] = int(mvalues[key]['PARALLEL'])
                    mvalues[key]['M'] = int(mvalues[key]['M'])*int(mvalues[key]['PARALLEL'])
            name_arg = name_arg+'_M'+str(int(mvalues[device_name]["M"]))
            size = 0

        logger.debug(f"Generating lef for {block_name}")
        if isinstance(size, int):
            for key in mvalues:
                assert int(mvalues[device_name]["NFIN"]) == int(mvalues[key]["NFIN"]), f"NFIN should be same for all devices in {name} {mvalues}"
                size_device = int(mvalues[key]["NF"])*int(mvalues[key]["M"])
                size = size + size_device
            no_units = ceil(size / (2*len(mvalues)))  # Factor 2 is due to NF=2 in each unit cell; needs to be generalized
            if any(x in block_name for x in ['DP', '_S']) and floor(sqrt(no_units/3)) >= 1:
                square_y = floor(sqrt(no_units/3))
            else:
                square_y = floor(sqrt(no_units))
            while no_units % square_y != 0:
                square_y -= 1
            yval = square_y
            xval = int(no_units / square_y)

        if 'SCM' in block_name:
            if int(mvalues[device_name_all[0]]["NFIN"])*int(mvalues[device_name_all[0]]["NF"])*int(mvalues[device_name_all[0]]["M"]) != \
                    int(mvalues[device_name_all[1]]["NFIN"])*int(mvalues[device_name_all[1]]["NF"])*int(mvalues[device_name_all[1]]["M"]):
                square_y = 1
                yval = square_y
                xval = int(no_units / square_y)

        block_args = {
            'primitive': generator_name,
            'value': mvalues[device_name]["NFIN"],
            'x_cells': xval,
            'y_cells': yval,
            'parameters': mvalues
        }
        if 'STACK' in mvalues[device_name].keys() and int(mvalues[device_name]["STACK"]) > 1:
            block_args['stack'] = int(mvalues[device_name]["STACK"])
        if vt:
            block_args['vt_type'] = vt[0]
        add_primitive(primitives, block_name, block_args)
    return True
