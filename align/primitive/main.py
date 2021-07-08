import sys
import datetime
import pathlib
import logging
import json
from copy import deepcopy
import importlib.util

from ..cell_fabric import gen_lef
from ..cell_fabric import positive_coord
from ..cell_fabric import gen_gds_json
from ..cell_fabric.pdk import Pdk
from math import sqrt, ceil,floor

from ..compiler.util import convert_to_unit

import logging
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
    return parameters

# TODO: Pass cell_pin and pattern to this function to begin with
def generate_MOS_primitive(pdkdir, block_name, primitive, height, nfin, x_cells, y_cells, pattern, vt_type, stack, parameters, pinswitch, bodyswitch):

    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('MOSGenerator', pdkdir)
    # TODO: THIS SHOULD NOT BE NEEDED !!!
    fin = int(nfin)
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    gate = 1
    shared_diff = 0 if any(primitive.startswith(f'{x}_') for x in ["LS_S","CMC_S","CCP_S"]) else 1
    uc = generator(pdk, height, fin, gate, gateDummy, shared_diff, stack, bodyswitch)
    x_cells, pattern = get_xcells_pattern(primitive, pattern, x_cells)
    parameters = get_parameters(primitive, parameters, nfin)

    def gen( pattern, routing):
        if 'NMOS' in primitive:
            uc.addNMOSArray( x_cells, y_cells, pattern, vt_type, routing, **parameters)
        else:
            uc.addPMOSArray( x_cells, y_cells, pattern, vt_type, routing, **parameters)
        return routing.keys()

    if primitive in ["Switch_NMOS_B", "Switch_PMOS_B"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'D')],
                            'G': [('M1', 'G')],
                            'B': [('M1', 'B')]})

    elif primitive in ["Switch_NMOS", "Switch_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S'), ('M1', 'B')],
                            'D': [('M1', 'D')],
                            'G': [('M1', 'G')]})

    elif primitive in ["Switch_GB_NMOS", "Switch_GB_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'D')],
                            'G': [('M1', 'G'), ('M1', 'B')]})

    elif primitive in ["DCL_NMOS_B", "DCL_PMOS_B"]:
        cell_pin = gen( 0, {'S': [('M1', 'S')],
                            'D': [('M1', 'G'), ('M1', 'D')],
                            'B': [('M1', 'B')]})

    elif primitive in ["DCL_NMOS", "DCL_PMOS"]:
        cell_pin = gen( 0, {'S': [('M1', 'S'), ('M1', 'B')],
                            'D': [('M1', 'G'), ('M1', 'D')]})

    elif primitive in ["CM_NMOS_B", "CM_PMOS_B"]:
        cell_pin = gen( 3,      {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["CM_NMOS", "CM_PMOS"]:
        cell_pin = gen( 3,     {'S':  [('M1', 'S'), ('M2', 'S'), ('M1', 'B'), ('M2', 'B')],
                                'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                'DB': [('M2', 'D')]})

    elif primitive in ["CMFB_NMOS_B", "CMFB_PMOS_B"]:
        cell_pin = gen( 3,     {'S':  [('M1', 'S'), ('M2', 'S')],
                                'DA': [('M1', 'D'), ('M1', 'G')],
                                'DB': [('M2', 'D')],
                                'GB': [('M2', 'G')],
                                'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["CMFB_NMOS", "CMFB_PMOS"]:
        cell_pin = gen( 3,     {'S':  [('M1', 'S'), ('M2', 'S'), ('M1', 'B'), ('M2', 'B')],
                                'DA': [('M1', 'D'), ('M1', 'G')],
                                'DB': [('M2', 'D')],
                                'GB': [('M2', 'G')]})

    elif primitive in ["Dummy_NMOS_B", "Dummy_PMOS_B"]:
        cell_pin = gen( 0,     {'S': [('M1', 'S'), ('M1', 'G')],
                                'D': [('M1', 'D')],
                                'B': [('M1', 'B')]})

    elif primitive in ["Dummy_NMOS", "Dummy_PMOS"]:
        cell_pin = gen( 0,     {'S': [('M1', 'S'), ('M1', 'G'), ('M1', 'B')],
                                'D': [('M1', 'D')]})

    elif primitive in ["Dcap_NMOS_B", "Dcap_PMOS_B"]:
        cell_pin = gen( 0,     {'S': [('M1', 'S'), ('M1', 'D')],
                                'G': [('M1', 'G')],
                                'B': [('M1', 'B')]})

    elif primitive in ["Dcap_NMOS", "Dcap_PMOS"]:
        cell_pin = gen( 0,     {'S': [('M1', 'S'), ('M1', 'D'), ('M1', 'B')],
                               'G': [('M1', 'G')]})

    elif primitive in ["Dummy1_NMOS_B", "Dummy1_PMOS_B"]:
        cell_pin = gen( 0,     {'S': [('M1', 'S'), ('M1', 'D'), ('M1', 'G')],
                                'B': [('M1', 'B')]})

    elif primitive in ["Dummy1_NMOS", "Dummy1_PMOS"]:
        cell_pin = gen( 0,     {'S': [('M1', 'S'), ('M1', 'D'), ('M1', 'G'), ('M1', 'B')]})

    elif primitive in ["SCM_NMOS_B", "SCM_PMOS_B"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["SCM_NMOS", "SCM_PMOS"]:
        cell_pin = gen(pattern, {'S': [('M1', 'S'), ('M2', 'S'), ('M1', 'B'), ('M2', 'B')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')]})

    elif primitive in ["CMC_S_NMOS_B", "CMC_S_PMOS_B"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'DA': [('M1', 'D')],
                                 'SB': [('M2', 'S')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["CMC_NMOS_B", "CMC_PMOS_B"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["CMC_NMOS", "CMC_PMOS"]:
        cell_pin = gen(pattern, {'S': [('M1', 'S'), ('M2', 'S'), ('M1', 'B'), ('M2', 'B')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'G':  [('M1', 'G'), ('M2', 'G')]})

    elif primitive in ["DP_NMOS_B", "DP_PMOS_B"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'GA': [('M1', 'G')],
                                 'GB': [('M2', 'G')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["DP_NMOS", "DP_PMOS"]:
        cell_pin = gen(pattern, {'S': [('M1', 'S'), ('M2', 'S'), ('M1', 'B'), ('M2', 'B')],
                                 'DA': [('M1', 'D')],
                                 'DB': [('M2', 'D')],
                                 'GA': [('M1', 'G')],
                                 'GB': [('M2', 'G')]})

    elif primitive in ["LS_S_NMOS_B", "LS_S_PMOS_B"]:
        cell_pin = gen(pattern, {'SA':  [('M1', 'S')],
                                 'SB': [('M2', 'S')],
                                 'DA': [('M1', 'D'), ('M1', 'G'), ('M2', 'G')],
                                 'DB': [('M2', 'D')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["CCP_NMOS_B", "CCP_PMOS_B"]:
        cell_pin = gen(pattern, {'S':  [('M1', 'S'), ('M2', 'S')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

    elif primitive in ["CCP_NMOS", "CCP_PMOS"]:
        cell_pin = gen(pattern, {'S': [('M1', 'S'), ('M2', 'S'), ('M1', 'B'), ('M2', 'B')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')]})

    elif primitive in ["CCP_S_NMOS_B", "CCP_S_PMOS_B"]:
        cell_pin = gen(pattern, {'SA': [('M1', 'S')],
                                 'SB': [('M2','S')],
                                 'DA': [('M1', 'D'),('M2', 'G')],
                                 'DB': [('M2', 'D'), ('M1', 'G')],
                                 'B':  [('M1', 'B'), ('M2', 'B')]})

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

def generate_Ring(pdkdir, block_name, x_cells, y_cells):

    pdk = Pdk().load(pdkdir / 'layers.json')
    generator = get_generator('RingGenerator', pdkdir)

    uc = generator(pdk)

    uc.addRing(x_cells, y_cells)

    return uc, ['Body']

def get_generator(name, pdkdir):
    pdk_dir_path = pdkdir
    if isinstance(pdkdir, str):
        pdk_dir_path = pathlib.Path(pdkdir)
    pdk_dir_stem = pdk_dir_path.stem

    try:  # is pdk an installed module
        module = importlib.import_module(pdk_dir_stem)
        return getattr(module, name)
    except:
        init_file = pdk_dir_path / '__init__.py'
        if init_file.is_file():  # is pdk a package
            spec = importlib.util.spec_from_file_location(pdk_dir_stem, pdk_dir_path / '__init__.py')
            module = importlib.util.module_from_spec(spec)
            sys.modules[pdk_dir_stem] = module
            spec.loader.exec_module(module)
            return getattr(module, name)
        else:  # is pdk old school (backward compatibility)
            spec = importlib.util.spec_from_file_location("primitive", pdkdir / 'primitive.py')
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            return getattr(module, name)


def generate_generic(pdkdir, parameters):

    pdk = Pdk().load(pdkdir / 'layers.json')
    primitive = get_generator(parameters["real_inst_type"], pdkdir)
    uc = primitive()
    uc.generate(
        ports=parameters["ports"],
        netlist_parameters=parameters["values"]
    )
    return uc, parameters["ports"]

'''def generate_primitive_parameters(primitive, parameters=None, pdkdir=pathlib.Path.cwd(), outputdir=pathlib.Path.cwd(), abstract_template_name=None, concrete_template_name=None):
    assert pdkdir.exists() and pdkdir.is_dir(), "PDK directory does not exist"
    uc = generate_primitive(block_name, **block_args, pdkdir=pdk_dir, outputdir=primitive_dir)'''

def generate_primitive_lef(name:str, attr:dict, available_block_lef:list, design_config:dict, uniform_height=False):
    """ Return commands to generate parameterized lef"""
    values=attr["values"]
    logger.debug(f"checking lef for: {name}, {values}")
    #for param, value in size.items():

    if name.lower() == 'generic':
        # TODO: how about hashing for unique names?        
        value_str = ''
        for key in sorted(values):
            val = values[key].replace('-','')
            value_str += f'_{key}_{val}'
        block_name = attr['real_inst_type'] + value_str
        block_parameters = {"parameters": deepcopy(attr), "primitive": name.lower()}      
        return block_name, block_parameters

    elif name.lower().startswith('cap'):
        #print("all val",values)
        if 'cap' in values.keys():
            if values["cap"]=="unit_size":
                size = design_config["unit_size_cap"]
            else:
                size = float('%g' % (round(values["cap"] * 1E15,4)))
            num_of_unit = float(size)/design_config["unit_size_cap"]
            block_name = name + '_' + str(int(size)) + 'f'
        else:
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
            size = size.replace('.','p').replace('-','_neg_')
            num_of_unit=1
            block_name = name + '_' + str(size)

        logger.debug(f"Found cap with size: {size}, {design_config['unit_size_cap']}")
        unit_block_name = 'Cap_' + str(design_config["unit_size_cap"]) + 'f'
        if block_name in available_block_lef:
            return block_name, available_block_lef[block_name]
        logger.debug(f'Generating lef for: {name}, {size}')
        if  num_of_unit > 128:
            return block_name, {
                'primitive': block_name,
                'value': int(size)
            }
        else:
            return unit_block_name, {
                'primitive': block_name,
                'value': design_config["unit_size_cap"]
            }
    elif name.lower().startswith('res'):
        if 'res' in values.keys():
            if values["res"]=="unit_size":
                size = design_config["unit_height_res"]
            else:
                size = '%g'%(round(values["res"],2))
        else :
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        block_name = name + '_' + str(size).replace('.','p')
        try:
            height = ceil(sqrt(float(size) / design_config["unit_height_res"]))
            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            logger.debug(f'Generating lef for: {block_name} {size}')
            return block_name, {
                'primitive': name,
                'value': (height, float(size))
            }
        except:
            return block_name, {
                'primitive': name,
                'value': (1, design_config["unit_height_res"])
            }
    else:
        if 'nmos' in name.lower():
            unit_size_mos = design_config["unit_size_nmos"]
        else:
            unit_size_mos = design_config["unit_size_pmos"]

        if unit_size_mos is None:
            """ 
            Transistor parameters:
                m:  number of instances
                nf: number of fingers
                w:  effective width of an instance (width of instance x number of fingers)
            """
            assert 'm' in values,  f'm: Number of instances not specified {values}'
            assert 'nf' in values, f'nf: Number of fingers not specified {values}'
            assert 'w' in values,  f'w: Width is not specified {values}'
            assert 'real_inst_type' in attr, f'vt: Transistor type is not specified {attr}'

            def x_by_y(m):
                y_sqrt = floor(sqrt(m))
                for y in range(y_sqrt, 0, -1):
                    if y == 1:
                        return m, y
                    elif m % y == 0:
                        return m//y, y

            m  = int(values['m'])
            nf = int(values['nf'])
            w = int(values['w']*1e9)
            vt = attr['real_inst_type']

            x, y = x_by_y(m)

            # TODO: Why is this needed???
            if name == 'Switch_NMOS_G':
                name = 'Switch_NMOS_B'
            elif name == 'Switch_PMOS_G':
                name = 'Switch_PMOS_B'

            block_name = f'{name}_{vt}_w{w}_m{m}'

            values['real_inst_type'] = vt

            block_args= {
                'primitive': name,
                'value': unit_size_mos,
                'x_cells': x,
                'y_cells': y,
                'value': 1, # hack. This is used as nfin later.
                'parameters':values
            }

            if 'stack' in values:
                assert nf == 1, f'Stacked transistor cannot have multiple fingers {nf}'
                block_args['stack']=int(values['stack'])
                block_name += f'_st'+str(int(values['stack']))
            else:
                block_name += f'_nf{nf}'

            block_name += f'_x{x}_y{y}'

            if block_name in available_block_lef:
                if block_args != available_block_lef[block_name]:
                    assert False, f'Two different transistors mapped to the same name {block_name}: {available_block_lef[block_name]} {block_args}'

            return block_name, block_args


        if "nfin" in values.keys():
            #FinFET design
            if values["nfin"]=="unit_size":
                size = unit_size_mos
            else:
                size = int(values["nfin"])
            name_arg ='nfin'+str(size)
        elif "w" in values.keys():
            #Bulk design
            if values["w"]=="unit_size":
                size = unit_size_mos
            else:
                size = int(values["w"]*1E+9/design_config["Gate_pitch"])                
            values["nfin"]=size
            name_arg ='nfin'+str(size)
        else:
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        if 'nf' in values.keys():
            if values['nf'] == 'unit_size':
                values['nf'] =size
            size=size*int(values["nf"])
            name_arg =name_arg+'_nf'+str(int(values["nf"]))

        if 'm' in values.keys():
            if values['m'] == 'unit_size':
                values['m'] = 1
            size=size*int(values["m"])
            name_arg =name_arg+'_m'+str(int(values["m"]))

        no_units = ceil(size / unit_size_mos)

        logger.debug('Generating lef for: %s %s', name, str(size))
        if isinstance(size, int):
            no_units = ceil(size / unit_size_mos)
            if any(x in name for x in ['DP','_S']) and floor(sqrt(no_units/3))>=1:
                square_y = floor(sqrt(no_units/3))
            else:
                square_y = floor(sqrt(no_units))
            while no_units % square_y != 0:
                square_y -= 1
            yval = square_y
            xval = int(no_units / square_y)
            block_name = f"{name}_{name_arg}_n{unit_size_mos}_X{xval}_Y{yval}"

            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            if name == 'Switch_NMOS_G':
                #TBD in celll generator
                name = 'Switch_NMOS_B'
            elif name == 'Switch_PMOS_G':
                name = 'Switch_PMOS_B'

            logger.debug(f"Generating parametric lef of:  {block_name} {name}")
            values["real_inst_type"]=attr["real_inst_type"]
            cell_gen_parameters= {
                'primitive': name,
                'value': unit_size_mos,
                'x_cells': xval,
                'y_cells': yval,
                'parameters':values
            }
            if 'stack' in values.keys():
                cell_gen_parameters['stack']=int(values["stack"])
                block_name = block_name+'_ST'+str(int(values["stack"]))
            #cell generator takes only one VT so doing a string search
            #To be fixed:
            if isinstance(attr["real_inst_type"],list):
                merged_vt='_'.join(attr["real_inst_type"])
            else:
                merged_vt=attr["real_inst_type"]

            vt= [vt for vt in design_config["vt_type"] if vt.lower() in  merged_vt]
            if vt:
                block_name = block_name+'_'+vt[0]
                cell_gen_parameters['vt_type']=vt[0]
            return block_name, cell_gen_parameters
        else:
            logger.debug("No proper parameters found for cell generation")
            block_name = name+"_"+size

    raise NotImplementedError(f"Could not generate LEF for {name}")

    #return uc

# WARNING: Bad code. Changing these default values breaks functionality.
def generate_primitive(block_name, primitive, height=28, x_cells=1, y_cells=1, pattern=1, value=12, vt_type='RVT', stack=1, parameters=None, pinswitch=0, bodyswitch=1, pdkdir=pathlib.Path.cwd(), outputdir=pathlib.Path.cwd(), abstract_template_name=None, concrete_template_name=None):

    assert pdkdir.exists() and pdkdir.is_dir(), "PDK directory does not exist"

    if primitive == 'generic':
        uc, cell_pin = generate_generic(pdkdir, parameters)
    elif 'MOS' in primitive:
        uc, cell_pin = generate_MOS_primitive(pdkdir, block_name, primitive, height, value, x_cells, y_cells, pattern, vt_type, stack, parameters, pinswitch, bodyswitch)
    elif 'cap' in primitive.lower():
        uc, cell_pin = generate_Cap(pdkdir, block_name, value)
        uc.setBboxFromBoundary()
    elif 'Res' in primitive:
        uc, cell_pin = generate_Res(pdkdir, block_name, height, x_cells, y_cells, value[0], value[1])
        uc.setBboxFromBoundary()
    elif 'ring' in primitive.lower():
        uc, cell_pin = generate_Ring(pdkdir, block_name, x_cells, y_cells)
        #uc.setBboxFromBoundary()
    else:
        raise NotImplementedError(f"Unrecognized primitive {primitive}")

    uc.computeBbox()
    if False:
        with open(outputdir / (block_name + '.debug.json'), "wt") as fp:
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
    positive_coord.json_pos(outputdir / (block_name + '.json'))
    gen_lef.json_lef(outputdir / (block_name + '.json'), block_name, cell_pin, bodyswitch, blockM, uc.pdk)

    with open( outputdir / (block_name + ".json"), "rt") as fp0, \
         open( outputdir / (block_name + ".gds.json"), 'wt') as fp1:
        gen_gds_json.translate(block_name, '', pinswitch, fp0, fp1, datetime.datetime( 2019, 1, 1, 0, 0, 0), uc.pdk)

    return uc
