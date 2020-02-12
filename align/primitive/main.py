import datetime
import pathlib
import logging
import json
import importlib.util

from ..cell_fabric import gen_lef
from ..cell_fabric import gen_gds_json
from ..cell_fabric.pdk import Pdk

logger = logging.getLogger(__name__)

def get_xcells_pattern( primitive, pattern, x_cells):
    if any(primitive.startswith(f'{x}_') for x in ["CM", "CMFB"]):
        # Dual transistor (current mirror) primitives
        # TODO: Generalize this (pattern is ignored)
        x_cells = 2*x_cells + 2
    elif any(primitive.startswith(f'{x}_') for x in ["SCM", "CMC", "DP", "CCP", "LS"]):
        # Dual transistor primitives
        x_cells = 2*x_cells
        # TODO: Fix difficulties associated with CC patterns matching this condition
        pattern = 2 if x_cells%4 != 0 else pattern ### CC is not possible; default is interdigitated
    return x_cells, pattern

def get_parameters(primitive, parameters, nfin):
    if parameters is None:
        parameters = {}
    if 'model' not in parameters:
        parameters['model'] = 'NMOS' if 'NMOS' in primitive else 'PMOS'
    parameters['nfin'] = nfin
    return parameters

# TODO: Pass cell_pin and pattern to this function to begin with
def generate_MOS_primitive(pdkdir, block_name, primitive, height, nfin, x_cells, y_cells, pattern, parameters, pinswitch):

    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('MOSGenerator', pdkdir)

    # TODO: THIS SHOULD NOT BE NEEDED !!!
    fin = height
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gate = 1

    uc = generator(pdk, fin, finDummy, gate, gateDummy)
    x_cells, pattern = get_xcells_pattern(primitive, pattern, x_cells)
    parameters = get_parameters(primitive, parameters, nfin)

    def gen( pattern, routing):
        if 'NMOS' in primitive:
            uc.addNMOSArray( x_cells, y_cells, pattern, routing, **parameters)
        else:
            uc.addPMOSArray( x_cells, y_cells, pattern, routing, **parameters)
        return routing.keys()

    if primitive in ["Switch_NMOS", "Switch_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'D')],
                            'G': [('M1', 'G')]})

    elif primitive in ["DCL_NMOS", "DCL_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'G'), ('M1', 'D')]})

    elif primitive in ["CM_NMOS", "CM_PMOS"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CMFB_NMOS", "CMFB_PMOS"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G')],
                                 'DB': [('M2', 'D')],
                                 'GB': [('M2', 'G')]})
    elif primitive in ["Dummy_NMOS", "Dummy_PMOS"]:
        cell_pin = gen( 3,      {'S': [('M1', 'S'), ('M1', 'G')],
                                 'D': [('M1', 'D')]})
    elif primitive in ["Dcap_NMOS", "Dcap_PMOS"]:
        cell_pin = gen( 3,      {'S': [('M1', 'S'), ('M1', 'D')],
                                'G': [('M1', 'G')]})
    elif primitive in ["Dummy1_NMOS", "Dummy1_PMOS"]:
        cell_pin = gen( 3,      {'S': [('M1', 'S'), ('M1', 'D'), ('M1', 'G')]})
    elif primitive in ["SCM_NMOS", "SCM_PMOS"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CMC_NMOS", "CMC_PMOS"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'DA': [('M1', 'D')],
                                 'SB': [('M2', 'S')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})


    elif primitive in ["CMC_NMOS_S", "CMC_PMOS_S"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})

    elif primitive in ["DP_NMOS", "DP_PMOS"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'GA': [('M1', 'G')],
                                 'GB': [('M2', 'G')]})

    elif primitive in ["LS_NMOS", "LS_PMOS"]:
        cell_pin = gen(pattern, {'SA':  [('M1', 'S')],
                                 'SB': [('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CCP_NMOS_S", "CCP_PMOS_S"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')]})

    elif primitive in ["CCP_NMOS", "CCP_PMOS"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'SB': [('M2','S')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')]}) 

    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")

    return uc, cell_pin

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
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy

    uc = generator(pdk, fin, finDummy)

    uc.addResArray(x_cells, y_cells, nfin, unit_res)

    return uc, ['PLUS', 'MINUS']

def get_generator(name, pdkdir):
    spec = importlib.util.spec_from_file_location("primitive", pdkdir / 'primitive.py')
    primitive = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(primitive)
    return getattr(primitive, name)

# WARNING: Bad code. Changing these default values breaks functionality.
def generate_primitive(block_name, primitive, height=12, x_cells=1, y_cells=1, pattern=1, value=12, parameters=None, pinswitch=0, pdkdir=pathlib.Path.cwd(), outputdir=pathlib.Path.cwd()):

    assert pdkdir.exists() and pdkdir.is_dir(), "PDK directory does not exist"

    if 'MOS' in primitive:
        uc, cell_pin = generate_MOS_primitive(pdkdir, block_name, primitive, height, value, x_cells, y_cells, pattern, parameters, pinswitch)
    elif 'cap' in primitive.lower():
        uc, cell_pin = generate_Cap(pdkdir, block_name, value)
        uc.setBboxFromBoundary()
    elif 'Res' in primitive:
        uc, cell_pin = generate_Res(pdkdir, block_name, height, x_cells, y_cells, value[0], value[1])
        uc.setBboxFromBoundary()
    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")

    with open(outputdir / (block_name + '.debug.json'), "wt") as fp:
        uc.computeBbox()
        json.dump( { 'bbox' : uc.bbox.toList(),
                     'globalRoutes' : [],
                     'globalRouteGrid' : [],
                     'terminals' : uc.terminals}
                    , fp, indent=2)

    with open(outputdir / (block_name + '.json'), "wt") as fp:
        uc.writeJSON( fp)
    if 'Cap' in primitive:
        blockM = 1
    else:
        blockM = 0         
    gen_lef.json_lef(outputdir / (block_name + '.json'), block_name, cell_pin, blockM, uc.pdk)
    with open( outputdir / (block_name + ".json"), "rt") as fp0, \
         open( outputdir / (block_name + ".gds.json"), 'wt') as fp1:
        gen_gds_json.translate(block_name, '', pinswitch, fp0, fp1, datetime.datetime( 2019, 1, 1, 0, 0, 0), uc.pdk)

    return uc
