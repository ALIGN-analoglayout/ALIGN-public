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

from collections import deque

from ..cell_fabric.pdk import Pdk
from .render_placement import dump_blocks

from .db import hierNode
from .checkers import gen_viewer_json, gen_transformation
from ..cell_fabric import gen_gds_json, transformation
from .. import PnR
from .toplevel import toplevel

logger = logging.getLogger(__name__)


def _generate_json_from_json(*, dbfile, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False, input_dir=None, toplevel=True, gds_json=True):

    with open(dbfile, "rt") as fp:
        hN = hierNode(json.load(fp))

    return _generate_json_from_hN(hN=hN, variant=variant, primitive_dir=primitive_dir, pdk_dir=pdk_dir, output_dir=output_dir, check=check, extract=extract, input_dir=input_dir, toplevel=toplevel, gds_json=gds_json)


def _generate_json_from_hN(*, hN, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False, input_dir=None, toplevel=True, gds_json=True):

    logger.debug(
        f"_generate_json_from_hN: {hN} {variant} {primitive_dir} {pdk_dir} {output_dir} {check} {extract} {input_dir} {toplevel} {gds_json}")

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


def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, *, nvariants=1, effort=0, check=False, extract=False, gds_json=False, render_placements=False, PDN_mode=False):

    pdk = Pdk().load(pdk_dir / 'layers.json')

    logger.info(f"Running Place & Route for {subckt}")

    # Create working & input directories
    working_dir = output_dir
    working_dir.mkdir(exist_ok=True)
    input_dir = working_dir / 'inputs'
    input_dir.mkdir(exist_ok=True)
    input_dir_wotap = working_dir / 'inputs' / 'wo_tap' 
    input_dir_wotap.mkdir(exist_ok=True)
    results_dir = working_dir / 'Results'

    # Generate file name inputs
    map_file = f'{subckt}.map'
    lef_file = f'{subckt}.lef'
    lef_file_wotap = f'{subckt}.wotap.lef'
    #verilog_file = f'{subckt}.v'
    verilog_file = f'{subckt}.verilog.json'
    pdk_file = 'layers.json'

    # Generate .map & .lef inputs for PnR
    with (input_dir / map_file).open(mode='wt') as mp, \
         (input_dir / lef_file).open(mode='wt') as lp:
        for file_ in primitive_dir.iterdir():
            logger.debug(f"found files {file_}")
            if file_.suffixes == ['.gds', '.json']:
                true_stem = file_.stem.split('.')[0]
                mp.write(f'{true_stem} {true_stem}.gds\n')
            elif file_.suffix == '.lef' and file_.stem != subckt:
                logger.debug(f"found lef files {file_}")
                lp.write(file_.read_text())
#        for file_ in (primitive_dir / 'wo_tap').iterdir():
#            if file_.suffix == '.lef' and file_.stem != subckt:
#                logger.debug(f"found lef files {file_}")
#                lp.write(file_.read_text())
#

    with (input_dir / lef_file_wotap).open(mode='wt') as lpwot:
        for file_ in (primitive_dir / 'wo_tap').iterdir():
            if file_.suffix == '.lef' and file_.stem != subckt:
                logger.debug(f"found lef files {file_}")
                lpwot.write(file_.read_text())

    #
    # TODO: Copying is bad ! Consider rewriting C++ code to accept fully qualified paths
    #

    # Copy verilog & const files
    (input_dir / verilog_file).write_text((topology_dir / verilog_file).read_text())
    for file_ in topology_dir.iterdir():
        if file_.suffix == '.json':
            (input_dir / file_.name).write_text(file_.read_text())

    # Copy pdk file
    (input_dir / pdk_file).write_text((pdk_dir / pdk_file).read_text())

    # Copy primitive json files
    for file_ in primitive_dir.iterdir():
        if file_.suffixes == ['.gds', '.json'] or file_.suffixes == ['.json']:
            (input_dir / file_.name).write_text(file_.read_text())
    # Copy primitives without tap to inputs/wo_tap/ directory
    for file_ in (primitive_dir / 'wo_tap').iterdir():
        if file_.suffixes == ['.gds', '.json'] or file_.suffixes == ['.json']:
            (input_dir_wotap / file_.name).write_text(file_.read_text())

    # Run pnr_compiler
    cmd = [str(x) for x in ('align.PnR', input_dir, lef_file,
                            verilog_file, map_file, pdk_file, subckt, nvariants, effort)]

    current_working_dir = os.getcwd()
    os.chdir(working_dir)
    DB = toplevel(cmd, PDN_mode=PDN_mode, pdk=pdk, render_placements=render_placements)
    #DB = PnR.toplevel(cmd)
    os.chdir(current_working_dir)

    # Copy generated (Cap) jsons from results_dir to working_dir
    # TODO: Cap arrays should eventually be generated by align.primitive
    #       at which point this hack will no longer be needed
    for file_ in results_dir.iterdir():
        if file_.suffixes == ['.json']:
            (working_dir / file_.name).write_text(file_.read_text())

    if check or extract or gds_json:

        def TraverseHierTree(topidx):
            """Find topoorder of routing copies: (start from last node)"""
            q = []
            visited = set()

            def TraverseDFS(idx):
                visited.add(idx)
                for bit in DB.hierTree[idx].Blocks:
                    if bit.child != -1 and bit.child not in visited:
                        TraverseDFS(bit.child)
                q.append(idx)
            # This isn't correct unless there is only one top level node
            TraverseDFS(topidx)
            return q

        possible_final_circuits = [(i, hN) for i, hN in enumerate(
            DB.hierTree) if hN.name == subckt]
        assert len(possible_final_circuits) > 1

        variants = collections.defaultdict(collections.defaultdict)
        for lidx, (topidx, _) in enumerate(possible_final_circuits[1:]):

            order = [(i, DB.CheckoutHierNode(i).name)
                     for i in TraverseHierTree(topidx)]
            assert order[-1][1] == subckt, f"Last in topological order should be the subckt {subckt} {order}"

            logger.info(f'order={order}')

            for idx, nm in order[:-1]:
                n_copy = DB.hierTree[idx].n_copy
                #assert 1 == DB.hierTree[idx].numPlacement
                i_placement = 0

                variant_name = f'{nm}_{n_copy}_{i_placement}'
                logger.info(
                    f'Processing top-down generated blocks {DB.hierTree[idx].numPlacement}: idx={idx} nm={nm} variant_name={variant_name}')

                hN = DB.CheckoutHierNode(idx)

                _generate_json_from_hN(hN=hN,
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

            logger.info(
                f'Processing top-down generated blocks: lidx={lidx} topidx={topidx} nm={nm} variant={variant}')

            hN = DB.CheckoutHierNode(idx)

            variants[variant].update(
                _generate_json_from_hN(hN=hN,
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
