# -*- coding: utf-8 -*-
"""
Created on Wed Feb 2 13:12:15 2022

@author: kunal
"""

from align.schema.types import set_context
import logging
import hashlib

from align.schema import SubCircuit, Model, Library

logger = logging.getLogger(__name__)


def gen_abstract_name(element, primitives):
    """ Return commands to generate parameterized lef"""
    self.library = Library(loadbuiltins=True)
    db = element.parent.parent.parent
    ele_def = db.find(element.generator)
    if isinstance(ele_def, SubCircuit):
        name = ele_def.name
    elif isinstance(ele_def, Model):
        # using base model name right now
        # need seperate generator for each model?
        name = db.find(ele_def.name).name
    else:
        # base model
        name = element.generator
    values = element.parameters
    logger.debug(f"Getting generator parameters for: {name}, {element}, {values}")

    if name == 'CAP':
        assert float(values["VALUE"]) or float(values["C"]), f"unidentified size {values} for {element.name}"
        if "C" in values:
            size = round(float(values["C"]) * 1E15, 4)
        elif 'VALUE' in values:
            size = round(float(values["VALUE"]) * 1E15, 4)
        assert size <= design_config["max_size_cap"], f"caps larger that {design_config['max_size_cap']}fF are not supported"

        # TODO: use float in name
        block_name = name + '_' + str(int(size)) + 'f'
        logger.debug(f"Generating capacitor for: {element.name} {name} {size}")
        element.add_abs_name(block_name)

        if block_name in primitives:
            return block_name, primitives[block_name]
        else:
            block_args = {
                'primitive': name,
                'value': int(size)
            }
            add_primitive(primitives, block_name, block_args)
            return True

    elif name == 'RES':
        assert float(values["VALUE"]) or float(values["R"]), f"unidentified size {values['VALUE']} for {element.name}"
        if "R" in values:
            size = round(float(values["R"]), 2)
        elif 'VALUE' in values:
            size = round(float(values["VALUE"]), 2)
        # TODO: use float in name
        if size.is_integer():
            size = int(size)
        block_name = name + '_' + str(size).replace('.', 'p')
        height = ceil(sqrt(float(size) / design_config["unit_height_res"]))
        logger.debug(f'Generating resistor for: {element.name} {name} {size}')
        element.add_abs_name(block_name)

        if block_name in primitives:
            return block_name, primitives[block_name]
        else:
            block_args = {
                'primitive': name,
                'value': (height, float(size))
            }
            add_primitive(primitives, block_name, block_args)
            return True

    elif name == 'generic' or get_generator(name.lower(), pdk_dir):
        value_str = ''
        if values:
            for key in sorted(values):
                val = str(values[key]).replace('-', '')
                value_str += f'_{key}_{val}'
        attr = {'ports': list(element.pins.keys()),
                'values': values if values else None,
                'real_inst_type': element.model.lower()
                }
        block_name = element.model + value_str
        element.add_abs_name(block_name)
        block_args = {"parameters": deepcopy(attr), "primitive": 'generic'}
        logger.debug(f"creating generic primitive {block_name} {block_args}")
        add_primitive(primitives, block_name, block_args)
        return True

    else:

        assert 'NMOS' in name or 'PMOS' in name, f'{name} is not recognized'

        subckt = element.parent.parent.parent.find(element.model)

        unit_size_mos = design_config["unit_size_mos"]

        if unit_size_mos is None:   # hack for align/pdk/finfet

            if isinstance(subckt, SubCircuit):
                vt = subckt.elements[0].model
                values = subckt.elements[0].parameters
                for e in subckt.elements:
                    assert vt == e.model, f'Primitive with different models not supported {vt} vs {e.model}'
                    assert values == e.parameters, f'Primitive with different parameters not supported {values} vs {e.parameters}'
            else:
                vt = element.model
                values = element.parameters

            assert 'M' in values,  f'm: Number of instances not specified {values}'
            assert 'NF' in values, f'nf: Number of fingers not specified {values}'

            m = int(values['M'])
            nf = int(values['NF'])

            def x_by_y(m):
                y_sqrt = floor(sqrt(m))
                for y in range(y_sqrt, 0, -1):
                    if y == 1:
                        return m, y
                    elif m % y == 0:
                        return m//y, y

            x, y = x_by_y(m)

            values['real_inst_type'] = vt

            # TODO: Stacking parallel transistors is illegal. To be addressed in compiler
            st = int(values.get('STACK', '1'))
            pl = int(values.get('PARALLEL', '1'))
            if st > 1 and (nf > 1 or pl > 1):
                assert False, 'Stacking multi-leg transistors not supported. Turn off MergeSeriesDevices'
            elif pl > 1 and nf != pl:
                assert False, 'Number of legs do not match'

            exclude_keys = ['M', 'real_inst_type']
            if 'W' in values:
                exclude_keys.append('NFIN')
            if 'PARALLEL' in values:
                exclude_keys.append('PARALLEL')
            if st > 1:
                exclude_keys.append('NF')
            elif 'STACK' in values:
                exclude_keys.append('STACK')

            sorted_keys = sorted(values.keys())
            block_name = f'{name}_{vt}_M{m}_'
            block_name += '_'.join([k+':'+str(values[k]) for k in sorted_keys if k not in exclude_keys])
            block_name += f"_{str(int(hashlib.sha256(block_name.encode('utf-8')).hexdigest(), 16) % 10**8)}"
            block_name += f'_X{x}_Y{y}'

            logger.debug(block_name)
            block_args = {
                'primitive': name,
                'x_cells': x,
                'y_cells': y,
                'parameters': values
            }

            if block_name in primitives:
                if block_args != primitives[block_name]:
                    assert False, f'Collision for {block_name}: new: {block_args} existing: {primitives[block_name]} '
                else:
                    logger.debug(f'{block_name} exists')
            else:
                add_primitive(primitives, block_name, block_args)
            element.add_abs_name(block_name)
            return True
        else:  # hacks for all other pdk's
            logger.debug(f"subckt definition found: {subckt}")
            vt = None
            values = {}
            vt_types_temp = []
            if isinstance(subckt, SubCircuit):
                for ele in subckt.elements:
                    values[ele.name] = ele.parameters
                    vt_types_temp.append(ele.model)
                vt_types = vt_types_temp[0]
                if "vt_type" in design_config:
                    vt = [vt.upper() for vt in design_config["vt_type"] if vt.upper() in vt_types]
            else:
                values[element.name] = element.parameters
                if "vt_type" in design_config:
                    vt = [vt.upper() for vt in design_config["vt_type"] if vt.upper() in element.model]
            device_name_all = [*values.keys()]
            device_name = device_name_all[0]

            if design_config["pdk_type"] == "FinFET":
                # FinFET design
                for key in values:
                    assert int(values[key]["NFIN"]), \
                        f"unrecognized NFIN of device {key}:{values[key]['NFIN']} in {name}"
                    assert unit_size_mos >= int(values[key]["NFIN"]), \
                        f"NFIN of device {key} in {name} should not be grater than {unit_size_mos}"
                    nfin = int(values[key]["NFIN"])
                name_arg = 'NFIN'+str(nfin)
            elif design_config["pdk_type"] == "Bulk":
                # Bulk design
                for key in values:
                    assert values[key]["W"] != str, f"unrecognized size of device {key}:{values[key]['W']} in {name}"
                    assert int(
                        float(values[key]["W"])*1E+9) % design_config["Fin_pitch"] == 0, \
                        f"Width of device {key} in {name} should be multiple of fin pitch:{design_config['Fin_pitch']}"
                    size = int(float(values[key]["W"])*1E+9/design_config["Fin_pitch"])
                    values[key]["NFIN"] = size
                name_arg = 'NFIN'+str(size)
            else:
                print(design_config["pdk_type"] + " pdk not supported")
                exit()

            if 'NF' in values[device_name].keys():
                for key in values:
                    assert int(values[key]["NF"]), f"unrecognized NF of device {key}:{values[key]['NF']} in {name}"
                    assert int(values[key]["NF"]) % 2 == 0, f"NF must be even for device {key}:{values[key]['NF']} in {name}"
                name_arg = name_arg+'_NF'+str(int(values[device_name]["NF"]))

            if 'M' in values[device_name].keys():
                for key in values:
                    assert int(values[key]["M"]), f"unrecognized M of device {key}:{values[key]['M']} in {name}"
                    if "PARALLEL" in values[key].keys() and int(values[key]['PARALLEL']) > 1:
                        values[key]["PARALLEL"] = int(values[key]['PARALLEL'])
                        values[key]['M'] = int(values[key]['M'])*int(values[key]['PARALLEL'])
                name_arg = name_arg+'_M'+str(int(values[device_name]["M"]))
                size = 0

            logger.debug(f"Generating lef for {name}")
            if isinstance(size, int):
                for key in values:
                    assert int(values[device_name]["NFIN"]) == int(values[key]["NFIN"]), f"NFIN should be same for all devices in {name} {values}"
                    size_device = int(values[key]["NF"])*int(values[key]["M"])
                    size = size + size_device
                no_units = ceil(size / (2*len(values)))  # Factor 2 is due to NF=2 in each unit cell; needs to be generalized
                if any(x in name for x in ['DP', '_S']) and floor(sqrt(no_units/3)) >= 1:
                    square_y = floor(sqrt(no_units/3))
                else:
                    square_y = floor(sqrt(no_units))
                while no_units % square_y != 0:
                    square_y -= 1
                yval = square_y
                xval = int(no_units / square_y)

            if 'SCM' in name:
                if int(values[device_name_all[0]]["NFIN"])*int(values[device_name_all[0]]["NF"])*int(values[device_name_all[0]]["M"]) != \
                   int(values[device_name_all[1]]["NFIN"])*int(values[device_name_all[1]]["NF"])*int(values[device_name_all[1]]["M"]):
                    square_y = 1
                    yval = square_y
                    xval = int(no_units / square_y)

            block_name = f"{name}_{name_arg}_N{unit_size_mos}_X{xval}_Y{yval}"

            block_args = {
                'primitive': name,
                'value': values[device_name]["NFIN"],
                'x_cells': xval,
                'y_cells': yval,
                'parameters': values
            }
            if 'STACK' in values[device_name].keys() and int(values[device_name]["STACK"]) > 1:
                block_args['stack'] = int(values[device_name]["STACK"])
                block_name = block_name+'_ST'+str(int(values[device_name]["STACK"]))
            if vt:
                block_args['vt_type'] = vt[0]
                block_name = block_name+'_'+vt[0]

            if block_name in primitives and block_args == primitives[block_name]:
                logger.debug(f'{block_name} exists')
                element.add_abs_name(block_name)
                return True
            else:
                element.add_abs_name(block_name)
                add_primitive(primitives, block_name, block_args)
                return True
