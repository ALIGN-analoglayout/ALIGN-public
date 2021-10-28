from align.schema import constraint
import pathlib
import os
import io
import sys
import logging
import collections
import json
import re
import itertools
#from IPython import embed
import copy

from collections import deque, defaultdict

from ..cell_fabric.pdk import Pdk

from .checkers import gen_viewer_json, gen_transformation
from ..cell_fabric import gen_gds_json, transformation
from .write_constraint import PnRConstraintWriter
from .. import PnR
from .toplevel import toplevel
from ..schema.hacks import VerilogJsonTop, VerilogJsonModule

logger = logging.getLogger(__name__)

from memory_profiler import profile

def _generate_json(*, hN, variant, primitive_dir, pdk_dir, output_dir, extract=False, input_dir=None, toplevel=True, gds_json=True):

    logger.debug(
        f"_generate_json: {hN} {variant} {primitive_dir} {pdk_dir} {output_dir} {extract} {input_dir} {toplevel} {gds_json}")

    cnv, d = gen_viewer_json(hN, pdkdir=pdk_dir, draw_grid=True, json_dir=str(primitive_dir),
                             extract=extract, input_dir=input_dir, toplevel=toplevel)

    if gds_json and toplevel:
        # Hack in Outline layer
        # Should be part of post processor
        d['terminals'].append(
            {"layer": "Outline", "netName": None, "netType": "drawing", "rect": d['bbox']})

    ret = {}

    ret['json'] = output_dir / f'{variant}.json'
    with open(ret['json'], 'wt') as fp:
        json.dump(d, fp=fp, indent=2)
    logger.info(f"OUTPUT json at {ret['json']}")

    ret['errfile'] = output_dir / f'{variant}.errors'
    with open(ret['errfile'], 'wt') as fp:
        for x in cnv.rd.shorts:
            fp.write(f'SHORT {x}\n')
        for x in cnv.rd.opens:
            fp.write(f'OPEN {x}\n')
        for x in cnv.rd.different_widths:
            fp.write( f'DIFFERENT WIDTH {x}\n')
        for x in cnv.drc.errors:
            fp.write(f'DRC ERROR {x}\n')
        for x in cnv.postprocessor.errors:
            fp.write(f'POSTPROCESSOR ERROR {x}\n')
    ret['errors'] = len(cnv.rd.shorts) + \
        len(cnv.rd.opens) + len(cnv.drc.errors)
    if ret['errors'] > 0:
        logger.error(f"{ret['errors']} LVS / DRC errors found !!!")
        logger.info(f"OUTPUT error file at {ret['errfile']}")

    if extract:
        ret['cir'] = output_dir / f'{variant}.cir'
        with open(ret['cir'], 'wt') as fp:
            cnv.pex.writePex(fp)
        logger.info(f"OUTPUT extracted netlist at {ret['cir']}")

    if gds_json:
        ret['python_gds_json'] = output_dir / f'{variant}.python.gds.json'
        with open(ret['json'], 'rt') as ifp:
            with open(ret['python_gds_json'], 'wt') as ofp:
                gen_gds_json.translate(
                    hN.name, '', 0, ifp, ofp, timestamp=None, p=cnv.pdk)
        logger.info(f"OUTPUT gds.json {ret['python_gds_json']}")

    return ret

def gen_constraint_files( verilog_d, input_dir):
    pnr_const_ds = {}
    for module in verilog_d['modules']:
        nm = module['name']
        pnr_const_ds[nm] = PnRConstraintWriter().map_valid_const(module['constraints'])

    constraint_files = set()
    for nm, constraints in pnr_const_ds.items():
        if len(constraints) == 0:
            continue
        fn = input_dir / f'{nm}.pnr.const.json'
        with open(fn, 'w') as outfile:
            json.dump(constraints, outfile, indent=4)

    return constraint_files, pnr_const_ds

def extract_capacitor_constraints( pnr_const_ds):
    cap_constraints = {}
    for nm, pnr_const_d in pnr_const_ds.items():
        cap_constraints[nm] = { const['cap_name'].upper() : const for const in pnr_const_d['constraints'] if const['const_name'] == "CC"}
    logger.debug( f'cap_constraints: {cap_constraints}')

    return cap_constraints


def remove_pg_pins(verilog_d: dict, subckt: str, pg_connections: dict):
    """remove_pg_pins

    Removes any ports related to power pins. PnR engine cannot connect to subcircuit power pins.
    It can connect to a primitive power pin

    Args:
        verilog_d (dict): spice dict from compiler
        subckt (str): name of sub-circuit
        pg_pins (list): list of power pins in subckt to be removed
    """
    logger.debug(f"removing power pins {pg_connections} from subckt {subckt}")
    modules_dict = {module['name']: module['parameters'] for module in verilog_d['modules']}

    if subckt in modules_dict:
        pass
    elif subckt.upper() in modules_dict:
        subckt = subckt.upper()
    else:
        assert False, f"{subckt} not found in design {modules_dict}"
    modules = [module for module in verilog_d['modules'] if module['name'] == subckt]
    assert len(modules) == 1, f"duplicate modules are found {modules}"
    module = modules[0]
    # Remove port from subckt level
    module['parameters'] = [p for p in module['parameters'] if p not in pg_connections.keys()]
    for inst in module['instances']:
        if inst['abstract_template_name'] in modules_dict:
            # Inst pins connected to pg_pins
            hier_pg_connections = {conn["formal"]: pg_connections[conn["actual"]] for conn in inst['fa_map'] if conn["actual"] in pg_connections}
            if len(hier_pg_connections) > 0:
                logger.debug(f"Removing instance {inst['instance_name']} pins connected to {hier_pg_connections}")
                inst['fa_map'] = [conn for conn in inst['fa_map'] if conn["formal"] not in hier_pg_connections]
                # Creates a copy of module with reduced pins
                new_name = modify_pg_conn_subckt(verilog_d, inst['abstract_template_name'], hier_pg_connections)
                inst['abstract_template_name'] = new_name
                remove_pg_pins(verilog_d, new_name, hier_pg_connections)
        else:
            inst['fa_map'] = [{'formal': conn['formal'],
                               'actual': pg_connections.get(conn["actual"], conn["actual"])} for conn in inst['fa_map']]
            logging.debug(f"leaf level node {inst['instance_name']} {inst['abstract_template_name']}")


def clean_if_extra(verilog_d, subckt):
    #Remove modules which are not instantiated
    all_inst = set([inst['abstract_template_name'] for module in verilog_d['modules'] for inst in module["instances"]]+[subckt])
    logger.debug(f"All used modules: {all_inst}")
    verilog_d['modules'] = [m for m in verilog_d['modules'] if m['name'] in all_inst]


def modify_pg_conn_subckt(verilog_d, subckt, pp):
    """
    creates a new subcircuit by removing power pins from a subcircuit definition
    and change internal connections within the subcircuit
    nm: new module
    """
    # TODO: remove redundant const

    nm = copy.copy([module for module in verilog_d['modules'] if module['name'] == subckt][0])

    nm['parameters'] = [p for p in nm['parameters'] if p not in pp]

    logger.debug(f"modifying subckt {nm['name']} {pp}")
    modules_dict = {module['name']: module['parameters'] for module in verilog_d['modules']}
    i = 0
    updated_ckt_name = subckt+'_PG'+str(i)
    while updated_ckt_name in modules_dict.keys():
        if modules_dict[updated_ckt_name] == nm['parameters']:
            logger.debug(f"using existing module {updated_ckt_name}")
            return updated_ckt_name
        else:
            i = i+1
            updated_ckt_name = subckt+'_PG'+str(i)
    nm['name'] = updated_ckt_name

    logger.debug(f"new module is added: {nm}")
    verilog_d['modules'].append(nm)
    return updated_ckt_name

def check_floating_pins(verilog_d):
    """exit in case of floating pins in design
    """
    for module in verilog_d["modules"]:
        all_nets = set(fa_map["actual"] for fa_map in inst['fa_map'] for inst in module["instances"])
        assert set(module["parameters"]).issubset(all_nets), f"floating port found in module {module['name']}"

def gen_leaf_cell_info( verilog_d, pnr_const_ds):
    non_leaves = { module['name'] for module in verilog_d['modules'] }
    leaves_called_in_an_instance = defaultdict(list)
    for module in verilog_d['modules']:
        nm = module['name']
        for instance in module['instances']:
            if 'abstract_template_name' in instance:
                atn = instance['abstract_template_name']
                if atn not in non_leaves:
                    leaves_called_in_an_instance[atn].append( (nm,instance['instance_name']))

    logger.debug( f'non_leaves: {non_leaves}')
    logger.debug( f'abstract_templates: {leaves_called_in_an_instance}')

    #
    # Capacitor hack --- Should be able to remove eventally
    #
    cap_constraints = extract_capacitor_constraints( pnr_const_ds)
    capacitors = defaultdict(list)
    for leaf, v in leaves_called_in_an_instance.items():
        for parent, instance_name in v:
            if parent in cap_constraints:
                if instance_name in cap_constraints[parent]:
                    logger.debug( f'parent: {parent} instance_name: {instance_name} leaf: {leaf} cap_constraints: {cap_constraints}')
                    capacitors[leaf].append( (parent,instance_name))

    # Remove generated capacitors
    leaves = set(leaves_called_in_an_instance.keys()).difference( set(capacitors.keys()))

    # Add unit caps to leaves
    for _, v in cap_constraints.items():
        for _, const in v.items():
            unit_cap = const['unit_capacitor']
            logger.debug( f'Adding unit_cap {unit_cap} to leaves')
            leaves.add( unit_cap)

    #
    # Guardring hack --- Should be able to remove eventally
    #
    for nm, pnr_const_d in pnr_const_ds.items():
        for const in pnr_const_d['constraints']:
            if const['const_name'] == "GuardRing":
                leaves.add(const['guard_ring_primitives'])

    logger.debug( f'leaves: {leaves}')
    return leaves, capacitors

def gen_leaf_collateral( leaves, primitives, primitive_dir):

    # Check if collateral files exist
    leaf_collateral = defaultdict(list)
    for k, v in primitives.items():
        atn = v['abstract_template_name']
        if atn not in leaves:
            logger.debug( f'abstract_template_name {atn} of {v} not in {leaves}')
            continue
        leaf = v['concrete_template_name']
        files = {}
        for suffix in ['.lef', '.json', '.gds.json']:
            fn = primitive_dir / f'{leaf}{suffix}'
            if fn.is_file():
                files[suffix] = str(fn)
            else:
                logger.warning( f'Collateral {suffix} for leaf {leaf} not found in {primitive_dir}')
        leaf_collateral[leaf] = files

    return leaf_collateral

def check_modules(verilog_d):
    all_module_pins = {}
    for mod in verilog_d["modules"]:
        all_module_pins[mod["name"]]=mod["parameters"]
    for mod in verilog_d["modules"]:
        for inst in mod["instances"]:
            assert 'abstract_template_name' in inst, f'no generated data for {inst}'
            if inst["abstract_template_name"] in all_module_pins:
                assert all(fm["formal"] in all_module_pins[inst["abstract_template_name"]] for fm in inst["fa_map"]), \
                    f"incorrect instantiation {inst['instance_name']} of module {inst['abstract_template_name']}, \
                     instance_pins: {inst['fa_map']}, module pins: {all_module_pins[inst['abstract_template_name']]}"

def write_verilog_json(verilog_d):
    return {"modules":[{"name":m.name,
                        "parameters": list(m.parameters),
                        "constraints": [mc.dict() for mc in m.constraints],
                        "instances": [mi.dict() for mi in m.instances],
                        } for m in verilog_d.modules],
        "global_signals":verilog_d.global_signals}

def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, *, primitives, nvariants=1, effort=0, extract=False,
                 gds_json=False, PDN_mode=False, router_mode='top_down', gui=False, skipGDS=False, steps_to_run,lambda_coeff,
                 reference_placement_verilog_json, nroutings=1, select_in_ILP=False, seed=0, use_analytical_placer=False):

    logger.info(f"Running Place & Route for {subckt} {router_mode} {steps_to_run}")
    # Generate file name inputs
    for cf in topology_dir.rglob('*.verilog.json'):
        if cf.stem == subckt+'.verilog':
            #File name and module name are small or both are capital letters
            assert subckt in [m.name for m in VerilogJsonTop.parse_file(cf).modules], f"file name {cf} does nto match module {subckt}"
        elif cf.stem.upper()==subckt+'.verilog':
            #File name is small and module name is caps
            assert subckt in [m.name for m in VerilogJsonTop.parse_file(cf).modules], f"file name {cf} does nto match module {subckt}"
        elif cf.stem == subckt.upper()+'.verilog':
            #File name is caps and module name is small
            subckt = subckt.upper()
            assert subckt in [m.name for m in VerilogJsonTop.parse_file(cf).modules], f"file name {cf} does nto match module {subckt}"

    map_file = f'{subckt}.map'
    lef_file = f'{subckt}.lef'
    verilog_file = f'{subckt}.verilog.json'
    pdk_file = 'layers.json'

    working_dir = output_dir
    input_dir = working_dir / 'inputs'
    results_dir = working_dir / 'Results'

    if '3_pnr:prep' in steps_to_run:
        # Create working & input directories
        working_dir.mkdir(exist_ok=True)
        input_dir.mkdir(exist_ok=True)
        verilog_d = VerilogJsonTop.parse_file((topology_dir / verilog_file))
        #with (topology_dir / verilog_file).open( 'rt') as fp:
        #    verilog_d = json.load(fp)
        check_modules(verilog_d)
        pg_connections = {p["actual"]:p["actual"] for p in verilog_d['global_signals']}
        check_floating_pins(verilog_d)
        remove_pg_pins(verilog_d, subckt, pg_connections)
        clean_if_extra(verilog_d, subckt)
        check_modules(verilog_d)

        logger.debug(f"updated verilog: {verilog_d}")
        with (input_dir/verilog_file).open("wt") as fp:
            json.dump(write_verilog_json(verilog_d), fp=fp, indent=2, default=str)
        # SMB: I want this to be in main (perhaps), or in the topology stage
        constraint_files, pnr_const_ds = gen_constraint_files( verilog_d, input_dir)
        logger.debug( f'constraint_files: {constraint_files}')

        leaves, capacitors = gen_leaf_cell_info( verilog_d, pnr_const_ds)

        with (working_dir / "__capacitors__.json").open("wt") as fp:
            json.dump( capacitors, fp=fp, indent=2)

        leaf_collateral = gen_leaf_collateral( leaves, primitives, primitive_dir)
        logger.debug(f'primitives: {primitives}')
        logger.debug( f'leaf_collateral: {leaf_collateral}')
        logger.debug( f'capacitors: {dict(capacitors)}')

        # Generate .map file for PnR
        with (input_dir / map_file).open(mode='wt') as mp:
            for _,v in primitives.items():
                a = v['abstract_template_name']
                c = v['concrete_template_name']
                if c in leaf_collateral:
                    assert '.lef' in leaf_collateral[c]
                else:
                    logger.warning( f'Unused primitive: {a} {c} excluded from map file')
                print( f'{a} {c}.gds', file=mp)

        # Generate .lef inputs for PnR
        with (input_dir / lef_file).open(mode='wt') as lp:
            logger.debug(f"lef files: {[pathlib.Path(v['.lef']) for k,v in leaf_collateral.items()]}")
            for k,v in leaf_collateral.items():
                lp.write(pathlib.Path(v['.lef']).read_text())

        #
        # TODO: Copying is bad ! Consider rewriting C++ code to accept fully qualified paths
        #

        # Copy verilog

        # (input_dir / verilog_file).write_text((topology_dir / verilog_file).read_text())

        # Copy pdk file
        (input_dir / pdk_file).write_text((pdk_dir / pdk_file).read_text())

        # Copy primitive json files
        for k,v in leaf_collateral.items():
            for suffix in ['.gds.json', '.json']:
                if suffix in v:
                    (input_dir / f'{k}{suffix}').write_text(pathlib.Path(v[suffix]).read_text())

    else:
        with (working_dir / "__capacitors__.json").open("rt") as fp:
            capacitors = json.load(fp)

    if '3_pnr:place' in steps_to_run or '3_pnr:route' in steps_to_run:

        with (pdk_dir / pdk_file).open( 'rt') as fp:
            scale_factor = json.load(fp)["ScaleFactor"]

        # Run pnr_compiler
        cmd = [str(x) for x in ('align.PnR', input_dir, lef_file,
                                verilog_file, map_file, pdk_file, subckt, nvariants, effort)]
        # print(cmd)

        current_working_dir = os.getcwd()
        os.chdir(working_dir)
        DB, results_name_map = toplevel(cmd, PDN_mode=PDN_mode, results_dir=None, router_mode=router_mode, gui=gui, skipGDS=skipGDS,
                                        lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                                        reference_placement_verilog_json=reference_placement_verilog_json, nroutings=nroutings,
                                        select_in_ILP=select_in_ILP, seed=seed, use_analytical_placer=use_analytical_placer)

        os.chdir(current_working_dir)

        # Copy generated cap jsons from results_dir to working_dir
        # TODO: Cap arrays should eventually be generated by align.primitive
        #       at which point this hack will no longer be needed

        for cap_template_name in capacitors.keys():
            for fn in results_dir.glob( f'{cap_template_name}_AspectRatio_*.json'):
                (working_dir / fn.name).write_text(fn.read_text())

    variants = collections.defaultdict(collections.defaultdict)

    if '3_pnr:check' in steps_to_run:
        for variant, ( path_name, layout_idx) in results_name_map.items():

            hN = DB.hierTree[layout_idx]
            result = _generate_json(hN=hN,
                                    variant=variant,
                                    pdk_dir=pdk_dir,
                                    primitive_dir=input_dir,
                                    input_dir=working_dir,
                                    output_dir=working_dir,
                                    extract=extract,
                                    gds_json=gds_json,
                                    toplevel=hN.isTop)

            if hN.isTop:
                variants[variant].update(result)

                if not skipGDS:
                    for tag, suffix in [('lef', '.lef'), ('gdsjson', '.gds.json')]:
                        path = results_dir / (variant + suffix)
                        assert path.exists()
                        variants[variant][tag] = path

    if '3_pnr:place' in steps_to_run or '3_pnr:route' in steps_to_run:
        logger.debug('Explicitly deleting DB...')
        del DB

    return variants
