from ..cell_fabric.pdk import Pdk
from ..cell_fabric import gen_gds_json
from ..cell_fabric import positive_coord
from ..cell_fabric import gen_lef
from ..schema.subcircuit import SubCircuit, Model

import sys
import datetime
import pathlib
import logging
import json
import importlib.util
from copy import deepcopy
from math import sqrt, ceil, floor
import hashlib

logger = logging.getLogger(__name__)


def get_xcells_pattern(primitive, pattern, x_cells):

    if any(primitive.startswith(f'{x}_') for x in ["CM", "CMFB"]):
        # TODO: Generalize this (pattern is ignored)
        x_cells = 2*x_cells + 2
    elif any(primitive.startswith(f'{x}_') for x in ["SCM", "CMC", "DP", "CCP", "LS"]):
        # Dual transistor primitives
        x_cells = 2*x_cells
        # TODO: Fix difficulties associated with CC patterns matching this condition
        pattern = 2 if x_cells % 4 != 0 else pattern  # CC is not possible; default is interdigitated
    return x_cells, pattern


def get_parameters(primitive, parameters, nfin):
    if parameters is None:
        parameters = {}
    if 'model' not in parameters:
        parameters['model'] = 'NMOS' if 'NMOS' in primitive else 'PMOS'
    return parameters

# TODO: Pass cell_pin and pattern to this function to begin with


def generate_MOS_primitive(pdkdir, block_name, primitive, height, nfin, x_cells, y_cells, pattern, vt_type, stack, parameters, pinswitch, bodyswitch):
    logger.debug(f"generating primitive {block_name}")
    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('MOSGenerator', pdkdir)
    # TODO: THIS SHOULD NOT BE NEEDED !!!
    fin = int(nfin)
    gateDummy = 3  # Total Dummy gates per unit cell: 2*gateDummy
    gate = 1
    shared_diff = 0 if any(primitive.name.startswith(f'{x}_') for x in ["LS_S", "CMC_S", "CCP_S"]) else 1
    uc = generator(pdk, height, fin, gate, gateDummy, shared_diff, stack, bodyswitch)
    x_cells, pattern = get_xcells_pattern(primitive.name, pattern, x_cells)
    parameters = get_parameters(primitive.name, parameters, nfin)

    def gen(pattern, routing):
        if 'NMOS' in primitive.name:
            uc.addNMOSArray(x_cells, y_cells, pattern, vt_type, routing, **parameters)
        else:
            uc.addPMOSArray(x_cells, y_cells, pattern, vt_type, routing, **parameters)
        return routing.keys()

    assert isinstance(primitive, SubCircuit)
    connections = {pin: [] for pin in primitive.pins}
    for ele in primitive.elements:
        for formal, actual in ele.pins.items():
            connections[actual].append((ele.name, formal))
    if len(primitive.elements) == 1:
        pattern = 0
    return uc, gen(pattern, connections)


def generate_Cap(pdkdir, block_name, unit_cap):

    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('CapGenerator', pdkdir)

    uc = generator(pdk)

    uc.addCap(unit_cap)

    return uc, ['PLUS', 'MINUS']


def generate_Res(pdkdir, block_name, height, x_cells, y_cells, nfin, unit_res):

    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('ResGenerator', pdkdir)

    fin = height
    finDummy = 4  # Total Dummy fins per unit cell: 2*finDummy

    uc = generator(pdk, fin, finDummy)

    uc.addResArray(x_cells, y_cells, nfin, unit_res)

    return uc, ['PLUS', 'MINUS']


def generate_Ring(pdkdir, block_name, x_cells, y_cells):

    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('RingGenerator', pdkdir)

    uc = generator(pdk)

    uc.addRing(x_cells, y_cells)

    return uc, ['Body']


def get_generator(name, pdkdir):
    if pdkdir is None:
        return False
    pdk_dir_path = pdkdir
    if isinstance(pdkdir, str):
        pdk_dir_path = pathlib.Path(pdkdir)
    pdk_dir_stem = pdk_dir_path.stem

    try:  # is pdk an installed module
        module = importlib.import_module(pdk_dir_stem)
    except ImportError:
        init_file = pdk_dir_path / '__init__.py'
        if init_file.is_file():  # is pdk a package
            spec = importlib.util.spec_from_file_location(pdk_dir_stem, pdk_dir_path / '__init__.py')
            module = importlib.util.module_from_spec(spec)
            sys.modules[pdk_dir_stem] = module
            spec.loader.exec_module(module)
        else:  # is pdk old school (backward compatibility)
            print(f"check {pdkdir/'primitive.py'}")
            spec = importlib.util.spec_from_file_location("primitive", pdkdir / 'primitive.py')
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
    return getattr(module, name, False) or getattr(module, name.lower(), False)


def generate_generic(pdkdir, parameters, netlistdir=None):
    primitive1 = get_generator(parameters["real_inst_type"], pdkdir)
    uc = primitive1()
    uc.generate(
        ports=parameters["ports"],
        netlist_parameters=parameters["values"],
        netlistdir=netlistdir
    )
    return uc, parameters["ports"]


def add_primitive(primitives, block_name, block_args):
    if block_name in primitives:
        if not primitives[block_name] == block_args:
            logger.warning(f"Distinct devices mapped to the same primitive {block_name}: \
                             existing: {primitives[block_name]}\
                             new: {block_args}")
    else:
        logger.debug(f"Found primitive {block_name} with {block_args}")
        primitives[block_name] = block_args

def intel_pdk(subckt, primitives):
    block_name = subckt.name
    vt = subckt.elements[0].model
    values = subckt.elements[0].parameters
    generator_name = subckt.name

    for e in subckt.elements:
        assert vt == e.model, f'Primitive with different models not supported {vt} vs {e.model}'
        assert values == e.parameters, f'Primitive with different parameters not supported {values} vs {e.parameters}'
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

    logger.debug(block_name)
    block_args = {
        'primitive': generator_name,
        'x_cells': x,
        'y_cells': y,
        'parameters': values
    }
    add_primitive(primitives, block_name, block_args)
    return True
# def finfet_pdk(subck, primitives):


def generate_primitive_param(subckt, primitives, pdk_dir, uniform_height=False):
    """ Return commands to generate parameterized lef"""
    # TODO model parameter can be improved
    block_name = subckt.name
    logger.info(f"Getting generator parameters for: {subckt}")
    generator_name = subckt.elements[0].generator
    layers_json = pdk_dir / "layers.json"
    with open(layers_json, "rt") as fp:
        pdk_data = json.load(fp)
    design_config = pdk_data["design_info"]

    if len(subckt.elements)==1:
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
        return True

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
        return True

    elif generator_name == 'generic' or get_generator(generator_name.lower(), pdk_dir):
        value_str = ''
        if values:
            for key in sorted(values):
                val = str(values[key]).replace('-', '')
                value_str += f'_{key}_{val}'
        attr = {'ports': list(subckt.pins),
                'values': values if values else None,
                'real_inst_type': generator_name.lower()
                }
        block_args = {"parameters": deepcopy(attr), "primitive": 'generic'}
        logger.debug(f"creating generic primitive {block_name} {block_args}")
        add_primitive(primitives, block_name, block_args)

    else:
        assert 'NMOS' in generator_name or 'PMOS' in generator_name, f'{generator_name} is not recognized'
        unit_size_mos = design_config["unit_size_mos"]

        if unit_size_mos is None:   # hack for align/pdk/finfet
            assert intel_pdk(subckt, primitives)
        else:  # hacks for all other pdk's
            if "vt_type" in design_config:
                vt = [vt.upper() for vt in design_config["vt_type"] if vt.upper() in subckt.elements[0].model]
            mvalues = {}
            for ele in subckt.elements:
                mvalues[ele.name] = ele.parameters
            device_name_all = [*mvalues.keys()]
            device_name = next(iter(mvalues))

            if design_config["pdk_type"] == "FinFET":
                # FinFET design
                for key in mvalues:
                    assert int(mvalues[key]["NFIN"]), \
                        f"unrecognized NFIN of device {key}:{mvalues[key]['NFIN']} in {block_name}"
                    assert unit_size_mos >= int(mvalues[key]["NFIN"]), \
                        f"NFIN of device {key} in {block_name} should not be grater than {unit_size_mos}"
                    nfin = int(mvalues[key]["NFIN"])
                name_arg = 'NFIN'+str(nfin)
            elif design_config["pdk_type"] == "Bulk":
                # Bulk design
                for key in mvalues:
                    assert mvalues[key]["W"] != str, f"unrecognized size of device {key}:{mvalues[key]['W']} in {block_name}"
                    assert int(
                        float(mvalues[key]["W"])*1E+9) % design_config["Fin_pitch"] == 0, \
                        f"Width of device {key} in {block_name} should be multiple of fin pitch:{design_config['Fin_pitch']}"
                    size = int(float(mvalues[key]["W"])*1E+9/design_config["Fin_pitch"])
                    mvalues[key]["NFIN"] = size
                name_arg = 'NFIN'+str(size)
            else:
                print(design_config["pdk_type"] + " pdk not supported")
                exit()

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


# WARNING: Bad code. Changing these default values breaks functionality.
def generate_primitive(block_name, primitive, height=28, x_cells=1, y_cells=1, pattern=1, value=12, vt_type='RVT', stack=1, parameters=None,
                       pinswitch=0, bodyswitch=1, pdkdir=pathlib.Path.cwd(), outputdir=pathlib.Path.cwd(), netlistdir=pathlib.Path.cwd(),
                       abstract_template_name=None, concrete_template_name=None):
    assert pdkdir.exists() and pdkdir.is_dir(), "PDK directory does not exist"
    assert isinstance(primitive, SubCircuit) \
        or isinstance(primitive, Model)\
        or primitive == 'generic' \
        or 'ring' in primitive, f"{block_name} definition: {primitive}"
    if primitive == 'generic':
        uc, cell_pin = generate_generic(pdkdir, parameters, netlistdir=netlistdir)
    elif 'ring' in primitive:
        uc, cell_pin = generate_Ring(pdkdir, block_name, x_cells, y_cells)
    elif 'MOS' in primitive.name:
        uc, cell_pin = generate_MOS_primitive(pdkdir, block_name, primitive, height, value, x_cells, y_cells,
                                              pattern, vt_type, stack, parameters, pinswitch, bodyswitch)
    elif 'CAP' in primitive.name:
        uc, cell_pin = generate_Cap(pdkdir, block_name, value)
        uc.setBboxFromBoundary()
    elif 'RES' in primitive.name:
        uc, cell_pin = generate_Res(pdkdir, block_name, height, x_cells, y_cells, value[0], value[1])
        uc.setBboxFromBoundary()
    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")
    uc.computeBbox()
    if False:
        with open(outputdir / (block_name + '.debug.json'), "wt") as fp:
            json.dump({'bbox': uc.bbox.toList(),
                       'globalRoutes': [],
                       'globalRouteGrid': [],
                       'terminals': uc.terminals}, fp, indent=2)

    with open(outputdir / (block_name + '.json'), "wt") as fp:
        uc.writeJSON(fp)
    if 'cap' in primitive:
        blockM = 1
    else:
        blockM = 0
    positive_coord.json_pos(outputdir / (block_name + '.json'))
    gen_lef.json_lef(outputdir / (block_name + '.json'), block_name, cell_pin, bodyswitch, blockM, uc.pdk)

    with open(outputdir / (block_name + ".json"), "rt") as fp0, \
            open(outputdir / (block_name + ".gds.json"), 'wt') as fp1:
        gen_gds_json.translate(block_name, '', pinswitch, fp0, fp1, datetime.datetime(2019, 1, 1, 0, 0, 0), uc.pdk)

    return uc
