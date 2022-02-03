import pathlib
import os
import io
import sys
import logging
import collections
import json
import re
import itertools

import copy

from collections import deque, defaultdict

from ..cell_fabric.pdk import Pdk

from .checkers import gen_viewer_json, gen_transformation
from ..cell_fabric import gen_gds_json, transformation
from .write_constraint import PnRConstraintWriter
from .. import PnR
from .toplevel import toplevel
from ..schema import constraint
from ..schema.hacks import List, FormalActualMap, VerilogJsonTop, VerilogJsonModule
from .manipulate_hierarchy import manipulate_hierarchy

import copy

logger = logging.getLogger(__name__)

from memory_profiler import profile


def _generate_json(*, hN, variant, primitive_dir, pdk_dir, output_dir, extract=False, input_dir=None, toplevel=True, gds_json=True,
                   pnr_const_ds=None):

    logger.debug(
        f"_generate_json: {hN} {variant} {primitive_dir} {pdk_dir} {output_dir} {extract} {input_dir} {toplevel} {gds_json}")

    cnv, d = gen_viewer_json(hN, pdkdir=pdk_dir, draw_grid=True, json_dir=str(primitive_dir),
                             extract=extract, input_dir=input_dir, toplevel=toplevel, pnr_const_ds=pnr_const_ds)

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


def gen_constraint_files(verilog_d, input_dir):
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
        constraint_files.add(fn)

    return constraint_files, pnr_const_ds


def load_constraint_files(input_dir):
    pnr_const_ds = dict()
    constraint_files = set(input_dir.glob('*.pnr.const.json'))
    for fn in constraint_files:
        nm = fn.name.split('.pnr.const.json')[0]
        with open(fn, 'r') as fp:
            pnr_const_ds[nm] = json.load(fp)
    return constraint_files, pnr_const_ds


def extract_capacitor_constraints(pnr_const_ds):
    cap_constraints = {}
    for nm, pnr_const_d in pnr_const_ds.items():
        cap_constraints[nm] = { const['cap_name'].upper() : const for const in pnr_const_d['constraints'] if const['const_name'] == "CC"}
    logger.debug( f'cap_constraints: {cap_constraints}')

    return cap_constraints




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
        for suffix in ['.placement_lef', '.lef', '.json', '.gds.json']:
            fn = primitive_dir / f'{leaf}{suffix}'
            if fn.is_file():
                files[suffix] = str(fn)
            else:
                logger.warning( f'Collateral {suffix} for leaf {leaf} not found in {primitive_dir}')
        leaf_collateral[leaf] = files

    return leaf_collateral

def write_verilog_json(verilog_d):
    return {"modules":[{"name":m.name,
                        "parameters": list(m.parameters),
                        "constraints": [mc.dict() for mc in m.constraints],
                        "instances": [mi.dict() for mi in m.instances],
                        } for m in verilog_d.modules],
        "global_signals":verilog_d.global_signals}

def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, *, primitives, nvariants=1, effort=0, extract=False,
                 gds_json=False, PDN_mode=False, router_mode='top_down', gui=False, skipGDS=False, steps_to_run,lambda_coeff,
                 reference_placement_verilog_json, nroutings=1, select_in_ILP=False, seed=0, use_analytical_placer=False, ilp_solver='symphony'):

    subckt = subckt.upper()

    logger.info(f"Running Place & Route for {subckt} {router_mode} {steps_to_run}")

    map_file = f'{subckt}.map'
    lef_file = f'{subckt}.lef'
    placement_lef_file = f'{subckt}.placement_lef'
    verilog_file = f'{subckt}.verilog.json'
    pdk_file = 'layers.json'

    working_dir = output_dir
    input_dir = working_dir / 'inputs'
    results_dir = working_dir / 'Results'

    if '3_pnr:prep' in steps_to_run:
        # Create working & input directories
        working_dir.mkdir(exist_ok=True)
        input_dir.mkdir(exist_ok=True)

        verilog_d = VerilogJsonTop.parse_file(topology_dir / f'{subckt}.verilog.json')
        

        logger.debug(f"updated verilog: {verilog_d}")
        with (input_dir/verilog_file).open("wt") as fp:
            json.dump(write_verilog_json(verilog_d), fp=fp, indent=2, default=str)

        # SMB: I want this to be in main (perhaps), or in the topology stage
        constraint_files, pnr_const_ds = gen_constraint_files(verilog_d, input_dir)
        logger.debug(f'Generated constraint files: {constraint_files}')

        leaves, capacitors = gen_leaf_cell_info( verilog_d, pnr_const_ds)

        with (working_dir / "__capacitors__.json").open("wt") as fp:
            json.dump( capacitors, fp=fp, indent=2)

        leaf_collateral = gen_leaf_collateral( leaves, primitives, primitive_dir)
        logger.debug(f'primitives: {primitives}')
        print('leaf collateral', leaf_collateral)
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

        with (input_dir / placement_lef_file).open(mode='wt') as lp:
            logger.debug(f"placement lef files: {[pathlib.Path(v['.placement_lef']) for k,v in leaf_collateral.items()]}")
            for k,v in leaf_collateral.items():
                lp.write(pathlib.Path(v['.placement_lef']).read_text())

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

        constraint_files, pnr_const_ds = load_constraint_files(input_dir)
        logger.debug(f'Loaded constraint files: {constraint_files}')

    if '3_pnr:place' in steps_to_run or '3_pnr:route' in steps_to_run:

        #
        # Hacks for partial routing
        #
        primitives_with_atn = defaultdict(list)
        for v in primitives.values():
            primitives_with_atn[v['abstract_template_name']].append(v)

        for k, v in primitives_with_atn.items():
            first_md = None
            first_primitive = None
            for primitive in v:
                if 'metadata' in primitive and 'partially_routed_pins' in primitive['metadata']:
                    md = primitive['metadata']['partially_routed_pins']
                    if first_md is None:
                        first_md = md
                        first_primitive = primitive
                    else:
                        if set(first_md.keys()) != set(md.keys()):
                            print('Pins differs between', first_primitive['concrete_template_name'], 'and', primitive['concrete_template_name'], first_md, md)
                    


        # Update connectivity for partially routed primitives
        for module in verilog_d['modules']:
            for instance in module['instances']:
                for primitive in primitives_with_atn[instance['abstract_template_name']]:
                    if 'metadata' in primitive and 'partially_routed_pins' in primitive['metadata']:
                        fa_map = {fa['formal']: fa['actual'] for fa in instance['fa_map']}
                        new_fa_map = List[FormalActualMap]()
                        for f, a in primitive['metadata']['partially_routed_pins'].items():
                            new_fa_map.append(FormalActualMap(formal=f, actual=fa_map[a]))
                        instance['fa_map'] = new_fa_map

        manipulate_hierarchy(verilog_d, subckt)



        with (pdk_dir / pdk_file).open( 'rt') as fp:
            scale_factor = json.load(fp)["ScaleFactor"]

        # Run pnr_compiler
        # print(cmd)

        current_working_dir = os.getcwd()
        os.chdir(working_dir)

        cmd = [str(x) for x in ('align.PnR', input_dir, lef_file,
                                verilog_file, map_file, pdk_file, subckt, nvariants, effort)]

        DB, results_name_map = toplevel(cmd, PDN_mode=PDN_mode, results_dir=None, router_mode=router_mode, gui=gui, skipGDS=skipGDS,
                                        lambda_coeff=lambda_coeff, scale_factor=scale_factor,
                                        reference_placement_verilog_json=reference_placement_verilog_json, nroutings=nroutings,
                                        select_in_ILP=select_in_ILP, seed=seed, use_analytical_placer=use_analytical_placer, ilp_solver=ilp_solver,
                                        primitives=primitives)

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
                                    toplevel=hN.isTop,
                                    pnr_const_ds=pnr_const_ds)

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
