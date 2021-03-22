import subprocess
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

from .db import hierNode
from .checkers import gen_viewer_json
from ..cell_fabric import gen_gds_json

logger = logging.getLogger(__name__)

def _generate_json_from_json( *, dbfile, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False, input_dir=None, toplevel=True, gds_json=True ):

    with open(dbfile,"rt") as fp:
        hN = hierNode(json.load(fp))

    return _generate_json_from_hN( hN=hN, variant=variant, primitive_dir=primitive_dir, pdk_dir=pdk_dir, output_dir=output_dir, check=check, extract=extract, input_dir=input_dir, toplevel=toplevel, gds_json=gds_json)
    

def _generate_json_from_hN( *, hN, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False, input_dir=None, toplevel=True, gds_json=True ):

    logger.debug( f"_generate_json_from_hN: {hN} {variant} {primitive_dir} {pdk_dir} {output_dir} {check} {extract} {input_dir} {toplevel} {gds_json}")

    ret = {}

    if not toplevel:
        # Check name matches n_copy number (top down flow)
        p2 = re.compile( r"^(\S+)_(\d+)_(\d+)$")
        m = p2.match(variant)
        assert m
        ncpy = int(m.groups()[1])
        assert ncpy == hN.n_copy, f"n_copy {hN.n_copy} should be same as in the variant name {variant} {ncpy}"

    res = gen_viewer_json( hN, pdkdir=pdk_dir, draw_grid=True, json_dir=str(primitive_dir), checkOnly=(check or extract or gds_json), extract=extract, input_dir=input_dir, toplevel=toplevel)

    if check or extract or gds_json:
        cnv, d = res
    else:
        d = res

    if gds_json and toplevel:
        # Hack in Outline layer
        # Should be part of post processor
        d['terminals'].append( { "layer": "Outline", "netName": None, "rect": d['bbox']})

    ret['json'] = output_dir / f'{variant}.json'
    with open( ret['json'], 'wt') as fp:
        json.dump( d, fp=fp, indent=2)
    logger.info(f"OUTPUT json at {ret['json']}")

    if check:
        ret['errfile'] = output_dir / f'{variant}.errors'
        with open(ret['errfile'], 'wt') as fp:
            for x in cnv.rd.shorts: fp.write( f'SHORT {x}\n')
            for x in cnv.rd.opens: fp.write( f'OPEN {x}\n')
            #for x in cnv.rd.different_widths: fp.write( f'DIFFERENT WIDTH {x}\n')
            for x in cnv.drc.errors: fp.write( f'DRC ERROR {x}\n')
        ret['errors'] = len(cnv.rd.shorts) + len(cnv.rd.opens) + len(cnv.drc.errors)
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
        with open( ret['json'], 'rt') as ifp:
            with open( ret['python_gds_json'], 'wt') as ofp:
                gen_gds_json.translate( hN.name, '', 0, ifp, ofp, timestamp=None, p=cnv.pdk)
        logger.info(f"OUTPUT gds.json {ret['python_gds_json']}")

    return ret

def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, *, nvariants=1, effort=0, check=False, extract=False, gds_json=False, render_placements=False):

    logger.info(f"Running Place & Route for {subckt}")

    # Check to make sure pnr_compiler is available to begin with
    assert 'ALIGN_HOME' in os.environ, "ALIGN_HOME not in environment"
    compiler_path = pathlib.Path(os.environ['ALIGN_HOME']).resolve() / 'PlaceRouteHierFlow' / 'pnr_compiler'
    assert compiler_path.is_file(), f"{compiler_path} not found. Has it been built?"

    sys.setdlopenflags(os.RTLD_GLOBAL|os.RTLD_LAZY)
    import PnR
    from .toplevel import toplevel

    # Create working & input directories
    working_dir = output_dir
    working_dir.mkdir(exist_ok=True)
    input_dir = working_dir / 'inputs'
    input_dir.mkdir(exist_ok=True)
    results_dir = working_dir / 'Results'

    # Generate file name inputs
    map_file = f'{subckt}.map'
    lef_file = f'{subckt}.lef'
    verilog_file = f'{subckt}.v'
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

    # Run pnr_compiler
    cmd = [str(x) for x in (compiler_path, input_dir, lef_file, verilog_file, map_file, pdk_file, subckt, nvariants, effort)]

    current_working_dir = os.getcwd()
    os.chdir(working_dir)
    DB = PnR.toplevel(cmd)
    #Python version; currently broken
    #DB = toplevel(cmd)
    os.chdir(current_working_dir)

    # Copy generated (Cap) jsons from results_dir to working_dir
    # TODO: Cap arrays should eventually be generated by align.primitive
    #       at which point this hack will no longer be needed
    for file_ in results_dir.iterdir():
        if file_.suffixes == ['.json']:
            (working_dir / file_.name).write_text(file_.read_text())

    if check or extract or gds_json:

        def TraverseHierTree( topidx):
            """Find topoorder of routing copies: (start from last node)"""
            q = []
            visited = set()
            def TraverseDFS( idx):
                visited.add(idx)
                for bit in DB.hierTree[idx].Blocks:
                    if bit.child != -1 and bit.child not in visited:
                        TraverseDFS( bit.child)
                q.append( idx)
            # This isn't correct unless there is only one top level node
            TraverseDFS( topidx)
            return q


        def dump_blocks( hN, DB):
            import plotly.graph_objects as go

            logger.info( f'{hN.parent=}')

            fig = go.Figure()

            def gen_trace_xy( placedBox):
                x0 = placedBox.LL.x
                y0 = placedBox.LL.y
                x1 = placedBox.UR.x
                y1 = placedBox.UR.y
                x = [x0,x1,x1,x0,x0]
                y = [y0,y0,y1,y1,y0]
                return x,y

            for blk in hN.Blocks:
                child_idx = blk.child
                inst = blk.instance[blk.selectedInstance]

                hovertext = f'{inst.name}<br>{inst.master} ({child_idx})<br>{str(inst.orient)} {inst.placedBox.LL.x} {inst.placedBox.LL.y} {inst.placedBox.UR.x} {inst.placedBox.UR.y}'

                x,y = gen_trace_xy( inst.placedBox)
                fig.add_trace(go.Scatter( x=x, y=y, mode='lines', name=hovertext, fill="toself", showlegend=False))

            fig.update_yaxes( scaleanchor = "x", scaleratio = 1)
            fig.update_layout( title=dict( text=f'{hN.name}_{hN.n_copy}'))
            fig.show()


        possible_final_circuits = [(i, hN) for i, hN in enumerate(DB.hierTree) if hN.name == subckt]
        assert len(possible_final_circuits) > 1

        for topidx,_ in possible_final_circuits[1:]:

            order = [(i,DB.CheckoutHierNode(i).name) for i in TraverseHierTree(topidx)]
            assert order[-1][1] == subckt, f"Last in topological order should be the subckt {subckt} {order}"

            logger.info( f'{order=}')

            for idx,nm in order[:-1]:
                n_copy = DB.hierTree[idx].n_copy
                #assert 1 == DB.hierTree[idx].numPlacement
                i_placement = 0

                variant_name = f'{nm}_{n_copy}_{i_placement}'
                logger.info(f'Processing top-down generated blocks {DB.hierTree[idx].numPlacement}: {idx=} {nm=} {variant_name=}')

                hN = DB.CheckoutHierNode(idx)

                if render_placements:
                    dump_blocks( hN, DB)

                _generate_json_from_hN( hN = hN,
                                variant = variant_name,
                                pdk_dir = pdk_dir,
                                primitive_dir = input_dir,
                                input_dir=working_dir,
                                output_dir=working_dir,
                                check=check,
                                extract=extract,
                                gds_json=gds_json,
                                toplevel=False)

            variants = collections.defaultdict(collections.defaultdict)

            # toplevel
            (idx,nm) = order[-1]

            n_copy = DB.hierTree[idx].n_copy
            #assert 1 == DB.hierTree[idx].numPlacement



            i_placement = 0
            variant = f'{nm}_{n_copy}'

            logger.info(f'Processing top-down generated blocks {DB.hierTree[idx].numPlacement}: {idx=} {nm=} {variant=}')

            hN = DB.CheckoutHierNode(idx)

            if render_placements:
                dump_blocks( hN, DB)

            variants[variant].update(
                _generate_json_from_hN( hN = hN,
                                        variant = variant,
                                        pdk_dir = pdk_dir,
                                        primitive_dir = input_dir,
                                        input_dir=working_dir,
                                        output_dir=working_dir,
                                        check=check,
                                        extract=extract,
                                        gds_json=gds_json,
                                        toplevel=True))


            for file_ in results_dir.iterdir():
                variant = file_.name.split('.')[0]
                if not variant.replace(f'{subckt}_', '').isdigit():
                    continue
                if file_.suffixes == ['.gds', '.json']:
                    variants[variant]['gdsjson'] = file_
                elif file_.suffixes == ['.lef']:
                    variants[variant]['lef'] = file_

    logger.info( 'Explicitly deleting DB...')
    del DB

    return variants
