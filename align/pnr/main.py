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

from collections import deque, defaultdict

from ..cell_fabric.pdk import Pdk

from .checkers import gen_viewer_json, gen_transformation
from ..cell_fabric import gen_gds_json, transformation
from .write_constraint import PnRConstraintWriter
from ..schema.constraint import ConstraintDB
from .. import PnR
from .toplevel import toplevel

logger = logging.getLogger(__name__)


def _generate_json(*, hN, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False, input_dir=None, toplevel=True, gds_json=True):

    logger.debug(
        f"_generate_json: {hN} {variant} {primitive_dir} {pdk_dir} {output_dir} {check} {extract} {input_dir} {toplevel} {gds_json}")

    ret = {}

    if not toplevel:
        # Check name matches n_copy number (top down flow)
        p2 = re.compile(r"^(\S+)_(\d+)_(\d+)$")
        m = p2.match(variant)
        assert m
        ncpy = int(m.groups()[1])
        assert ncpy == hN.n_copy, f"n_copy {hN.n_copy} should be same as in the variant name {variant} {ncpy}"

    res = gen_viewer_json(hN, pdkdir=pdk_dir, draw_grid=True, json_dir=str(primitive_dir), checkOnly=(
        check or extract or gds_json), extract=extract, input_dir=input_dir, toplevel=toplevel)

    if check or extract or gds_json:
        cnv, d = res
    else:
        d = res

    if gds_json and toplevel:
        # Hack in Outline layer
        # Should be part of post processor
        d['terminals'].append(
            {"layer": "Outline", "netName": None, "rect": d['bbox']})

    ret['json'] = output_dir / f'{variant}.json'
    with open(ret['json'], 'wt') as fp:
        json.dump(d, fp=fp, indent=2)
    logger.info(f"OUTPUT json at {ret['json']}")

    if check:
        ret['errfile'] = output_dir / f'{variant}.errors'
        with open(ret['errfile'], 'wt') as fp:
            for x in cnv.rd.shorts:
                fp.write(f'SHORT {x}\n')
            for x in cnv.rd.opens:
                fp.write(f'OPEN {x}\n')
            #for x in cnv.rd.different_widths: fp.write( f'DIFFERENT WIDTH {x}\n')
            for x in cnv.drc.errors:
                fp.write(f'DRC ERROR {x}\n')
        ret['errors'] = len(cnv.rd.shorts) + \
            len(cnv.rd.opens) + len(cnv.drc.errors)
        if ret['errors'] > 0:
            logger.error(f"{ret['errors']} LVS / DRC errors found !!!")
            logger.info(f"OUTPUT error file at {ret['errors']}")

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


def gen_leaf_cell_info( verilog_d, input_dir, primitive_dir):
    

    non_leaves = set()
    templates_called_in_an_instance = defaultdict(list)

    pnr_const_ds = {}
    for module in verilog_d['modules']:
        nm = module['name']
        pnr_const_ds[nm] = PnRConstraintWriter().map_valid_const(ConstraintDB(__root__=module['constraints'], check=False))
        non_leaves.add( nm)
        for instance in module['instances']:
            templates_called_in_an_instance[instance['template_name']].append( (nm,instance['instance_name']))

    constraint_files = set()
    for nm, constraints in pnr_const_ds.items():
        if len(constraints) == 0:
            continue
        fn = input_dir / f'{nm}.pnr.const.json'
        with open(fn, 'w') as outfile:
            json.dump(constraints, outfile, indent=4)

    cap_constraints = {}
    for nm, pnr_const_d in pnr_const_ds.items():
        cap_constraints[nm] = { const['cap_name'] : const for const in pnr_const_d['constraints'] if const['const_name'] == "CC"}

    leaves = set(templates_called_in_an_instance.keys()).difference( non_leaves)

    logger.debug( f'non_leaves: {non_leaves} leaves: {leaves}')

    logger.debug( f'templates: {templates_called_in_an_instance}')

    # Find capacitors
    capacitors = defaultdict(list)
    for leaf in leaves:
        for parent, instance_name in templates_called_in_an_instance[leaf]:
            if parent in cap_constraints:
                if instance_name in cap_constraints[parent]:
                    logger.debug( f'parent: {parent} instance_name: {instance_name} leaf: {leaf} cap_constraints: {cap_constraints}')
                    capacitors[leaf].append( (parent,instance_name))


    for k, v in capacitors.items():
        if len(v) > 1:
            logger.error( f'CC Capacitor with template_name {v} instantiated more than once: {dict(v)}')

    # Remove generated capacitors
    leaves = leaves.difference( set(capacitors.keys()))

    # Add unit caps to leaves
    for _, v in cap_constraints.items():
        for _, const in v.items():
            unit_cap = const['unit_capacitor']
            logger.debug( f'Adding unit_cap {unit_cap} to leaves')
            leaves.add( unit_cap)

    # Check if collateral files exist
    leaf_collateral = {}
    for leaf in leaves:
        files = {}
        for suffix in ['.lef', '.json', '.gds.json']:
            fn = primitive_dir / f'{leaf}{suffix}'
            if fn.is_file():
                files[suffix] = str(fn)
            else:
                logger.error( f'Collateral {suffix} for leaf {leaf} not found in {primitive_dir}')
        leaf_collateral[leaf] = files

    return leaf_collateral, constraint_files, capacitors

def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, *, nvariants=1, effort=0, check=False, extract=False, gds_json=False, render_placements=False, PDN_mode=False):

    logger.info(f"Running Place & Route for {subckt}")

    # Create working & input directories
    working_dir = output_dir
    working_dir.mkdir(exist_ok=True)
    input_dir = working_dir / 'inputs'
    input_dir.mkdir(exist_ok=True)
    results_dir = working_dir / 'Results'

    # Generate file name inputs
    map_file = f'{subckt}.map'
    lef_file = f'{subckt}.lef'
    #verilog_file = f'{subckt}.v'
    verilog_file = f'{subckt}.verilog.json'
    pdk_file = 'layers.json'

    with (topology_dir / verilog_file).open( "rt") as fp:
        verilog_d = json.load( fp)

    leaf_collateral, constraint_files, capacitors = gen_leaf_cell_info( verilog_d, input_dir, primitive_dir)
    logger.debug( f'leaf_collateral: {leaf_collateral}')
    logger.debug( f'constraint_files: {constraint_files}')
    logger.debug( f'capacitors: {dict(capacitors)}')

    # Generate .map file for PnR
    with (input_dir / map_file).open(mode='wt') as mp:
        for k,v in leaf_collateral.items():
            assert '.gds.json' in v
            print( f'{k} {k}.gds', file=mp)

    # Generate .lef inputs for PnR
    with (input_dir / lef_file).open(mode='wt') as lp:
        for k,v in leaf_collateral.items():
            lp.write(pathlib.Path(v['.lef']).read_text())

    #
    # TODO: Copying is bad ! Consider rewriting C++ code to accept fully qualified paths
    #

    # Copy verilog
    (input_dir / verilog_file).write_text((topology_dir / verilog_file).read_text())

    # Copy pdk file
    (input_dir / pdk_file).write_text((pdk_dir / pdk_file).read_text())

    # Copy primitive json files
    for k,v in leaf_collateral.items():
        for suffix in ['.gds.json', '.json']:
            (input_dir / f'{k}{suffix}').write_text(pathlib.Path(v[suffix]).read_text())

    # Run pnr_compiler
    cmd = [str(x) for x in ('align.PnR', input_dir, lef_file,
                            verilog_file, map_file, pdk_file, subckt, nvariants, effort)]

    current_working_dir = os.getcwd()
    os.chdir(working_dir)
    DB, results_name_map = toplevel(cmd, PDN_mode=PDN_mode, render_placements=render_placements, results_dir=None)
    os.chdir(current_working_dir)

    # Copy generated cap jsons from results_dir to working_dir
    # TODO: Cap arrays should eventually be generated by align.primitive
    #       at which point this hack will no longer be needed
    for cap_template_name in capacitors.keys():
        for fn in results_dir.glob( f'{cap_template_name}_AspectRatio_*.json'):
            (working_dir / fn.name).write_text(fn.read_text())

    if check or extract or gds_json:

        def TraverseHierTree(topidx):
            """Find topoorder of routing copies: (start from topidx)"""
            q = []
            visited = set()
            def TraverseDFS(idx):
                visited.add(idx)
                for bit in DB.hierTree[idx].Blocks:
                    if bit.child != -1 and bit.child not in visited:
                        TraverseDFS(bit.child)
                q.append(idx)
            TraverseDFS(topidx)
            return q

        possible_final_circuits = [(i, hN) for i, hN in enumerate(DB.hierTree) if hN.name == subckt]
        assert len(possible_final_circuits) > 1

        variants = collections.defaultdict(collections.defaultdict)
        for lidx, (topidx, _) in enumerate(possible_final_circuits[1:]):

            order = [(i, DB.CheckoutHierNode(i, -1).name) for i in TraverseHierTree(topidx)]
            assert order[-1][1] == subckt, f"Last in topological order should be the subckt {subckt} {order}"

            logger.info(f'order={order}')

            for idx, nm in order[:-1]:
                n_copy = DB.hierTree[idx].n_copy
                #assert 1 == DB.hierTree[idx].numPlacement
                i_placement = lidx

                variant_name = f'{nm}_{n_copy}_{i_placement}'
                _generate_json(hN=DB.hierTree[idx],
                               variant=variant_name,
                               pdk_dir=pdk_dir,
                               primitive_dir=input_dir,
                               input_dir=working_dir,
                               output_dir=working_dir,
                               check=check,
                               extract=extract,
                               gds_json=gds_json,
                               toplevel=False)

            # toplevel
            (idx, nm) = order[-1]
            assert idx == topidx

            variant = f'{nm}_{lidx}'

            logger.info( f'Processing top-down generated blocks: lidx={lidx} topidx={topidx} nm={nm} variant={variant}')

            variants[variant].update(
                _generate_json(hN=DB.hierTree[idx],
                               variant=variant,
                               pdk_dir=pdk_dir,
                               primitive_dir=input_dir,
                               input_dir=working_dir,
                               output_dir=working_dir,
                               check=check,
                               extract=extract,
                               gds_json=gds_json,
                               toplevel=True))

            for tag, suffix in [('lef', '.lef'), ('gdsjson', '.gds.json')]:
                path = results_dir / (variant + suffix)
                assert path.exists()
                variants[variant][tag] = path

    logger.info('Explicitly deleting DB...')
    del DB

    return variants
