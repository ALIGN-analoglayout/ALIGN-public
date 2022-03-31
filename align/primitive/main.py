from ..cell_fabric.pdk import Pdk
from ..cell_fabric import gen_gds_json
from ..cell_fabric import positive_coord
from ..cell_fabric import gen_lef
from ..schema.subcircuit import SubCircuit
import copy
import sys
import datetime
import pathlib
import logging
import importlib.util

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


def generate_primitives(primitive_lib, pdk_dir, primitive_dir, netlist_dir):
    primitives = dict()
    for primitive in primitive_lib:
        if isinstance(primitive, SubCircuit):
            generate_primitive_param(primitive, primitives, pdk_dir)
    for block_name, block_args in primitives.items():
        logger.debug(f"Generating primitive {block_name}")
        if block_args['primitive'] != 'generic' and block_args['primitive'] != 'guard_ring':
            primitive_def = primitive_lib.find(block_args['abstract_template_name'])
            assert primitive_def is not None, f"unavailable primitive definition {block_name} of type {block_args['abstract_template_name']}"
        else:
            primitive_def = block_args['primitive']
        block_args.pop("primitive", None)
        uc = generate_primitive(block_name, primitive_def,  ** block_args,
                                pdkdir=pdk_dir, outputdir=primitive_dir, netlistdir=netlist_dir)
        if hasattr(uc, 'metadata'):
            primitives[block_name]['metadata'] = copy.deepcopy(uc.metadata)
    return primitives


def generate_primitive_param(subckt: SubCircuit, primitives: list, pdk_dir: pathlib.Path, uniform_height=False):
    """ Return commands to generate parameterized lef"""
    assert isinstance(subckt, SubCircuit), f"invalid input for primitive generator {subckt}"
    spec = importlib.util.spec_from_file_location("gen_param", pdk_dir / 'gen_param.py')
    modules = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(modules)
    assert modules.gen_param(subckt, primitives, pdk_dir), f"unabble to generate primitive {subckt}"


# WARNING: Bad code. Changing these default values breaks functionality.
def generate_primitive(block_name, primitive, height=28, x_cells=1, y_cells=1, pattern=1, value=12, vt_type='RVT', stack=1, parameters=None,
                       pinswitch=0, bodyswitch=1, pdkdir=pathlib.Path.cwd(), outputdir=pathlib.Path.cwd(), netlistdir=pathlib.Path.cwd(),
                       abstract_template_name=None, concrete_template_name=None):
    assert pdkdir.exists() and pdkdir.is_dir(), "PDK directory does not exist"
    assert isinstance(primitive, SubCircuit) \
        or primitive == 'generic' \
        or 'ring' in primitive, f"{block_name} definition: {primitive}"
    if primitive == 'generic':
        uc, _ = generate_generic(pdkdir, parameters, netlistdir=netlistdir)
    elif 'ring' in primitive:
        uc, _ = generate_Ring(pdkdir, block_name, x_cells, y_cells)
    elif 'MOS' == primitive.generator['name']:
        uc, _ = generate_MOS_primitive(pdkdir, block_name, primitive, height, value, x_cells, y_cells,
                                       pattern, vt_type, stack, parameters, pinswitch, bodyswitch)
    elif 'CAP' == primitive.generator['name']:
        uc, _ = generate_Cap(pdkdir, block_name, value)
        uc.setBboxFromBoundary()
    elif 'RES' == primitive.generator['name']:
        uc, _ = generate_Res(pdkdir, block_name, height, x_cells, y_cells, value[0], value[1])
        uc.setBboxFromBoundary()
    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")
    uc.computeBbox()

    with open(outputdir / (block_name + '.json'), "wt") as fp:
        uc.writeJSON(fp)
    if 'cap' in primitive:
        blockM = 1
    else:
        blockM = 0
    positive_coord.json_pos(outputdir / (block_name + '.json'))
    gen_lef.json_lef(outputdir / (block_name + '.json'), block_name, bodyswitch, blockM, uc.pdk, mode='placement')
    gen_lef.json_lef(outputdir / (block_name + '.json'), block_name, bodyswitch, blockM, uc.pdk, mode='routing')

    #with open(outputdir / (block_name + ".json"), "rt") as fp0, \
    #        open(outputdir / (block_name + ".gds.json"), 'wt') as fp1:
    #    gen_gds_json.translate(block_name, '', pinswitch, fp0, fp1, datetime.datetime(2019, 1, 1, 0, 0, 0), uc.pdk)

    return uc
