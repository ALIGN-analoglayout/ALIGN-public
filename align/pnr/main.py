import subprocess
import pathlib
import os
import logging
import collections
import json
import re

from .db import hierNode
from .checkers import gen_viewer_json

logger = logging.getLogger(__name__)

def _generate_json(dbfile, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False, input_dir=None):

    ret = {}
    with open(dbfile,"rt") as fp:
        hN = hierNode(json.load(fp))
    res = gen_viewer_json( hN, pdk=pdk_dir, draw_grid=True, json_dir=str(primitive_dir), checkOnly=(check or extract), extract=extract, input_dir=input_dir)

    if check or extract:
        cnv, d = res
    else:
        d = res

    with open( output_dir / f'{variant}.json', 'wt') as fp:
        json.dump( d, fp=fp, indent=2)
    ret['json'] = output_dir / f'{variant}.json'

    if check:
        with open(output_dir / f'{variant}.errors', 'wt') as fp:
            fp.write('\n'.join([f'SHORT {x}' for x in cnv.rd.shorts]))
            fp.write('\n'.join([f'OPEN {x}' for x in cnv.rd.opens]))
            fp.write('\n'.join([f'DIFFERENT WIDTH {x}' for x in cnv.rd.different_widths]))
            fp.write('\n'.join([f'DRC ERROR {x}' for x in cnv.drc.errors]))
        ret['errfile'] = output_dir / f'{variant}.errors'

        ret['errors'] = len(cnv.rd.shorts) + len(cnv.rd.opens) + len(cnv.rd.different_widths) + len(cnv.drc.errors)

    if extract:
        with open(output_dir / f'{variant}.cir', 'wt') as fp:
            cnv.pex.writePex(fp)
        ret['cir'] = output_dir / f'{variant}.cir'

    return ret

def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, nvariants=1, effort=0, check=False, extract=False):

    # Check to make sure pnr_compiler is available to begin with
    assert 'ALIGN_HOME' in os.environ, "ALIGN_HOME not in environment"
    compiler_path = pathlib.Path(os.environ['ALIGN_HOME']).resolve() / 'PlaceRouteHierFlow' / 'pnr_compiler'
    assert compiler_path.is_file(), f"{compiler_path} not found. Has it been built?"

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
        if file_.suffix == '.const':
            (input_dir / file_.name).write_text(file_.read_text())

    # Copy pdk file
    (input_dir / pdk_file).write_text((pdk_dir / pdk_file).read_text())

    # Copy primitive json files
    for file_ in primitive_dir.iterdir():
        if file_.suffixes == ['.gds', '.json']:
            (input_dir / file_.name).write_text(file_.read_text())

    # Dump out intermediate states
    if check or extract:
        os.environ['PNRDB_SAVE_STATE'] = ''

    # Run pnr_compiler
    cmd = [str(x) for x in (compiler_path, input_dir, lef_file, verilog_file, map_file, pdk_file, subckt, nvariants, effort)]
    try:
        ret = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, encoding='utf-8', cwd=working_dir)
        logger.debug(f'{ret.stdout}')
    except subprocess.CalledProcessError as e:
        logger.error(f"Call to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        return {}

    def find_variant_names( nm):
        p = re.compile( '^(.*)_(\d+)\.db\.json$')
        variant_names = []
        for file_ in results_dir.iterdir():
            m = p.match( file_.name)
            if m and m.groups()[0] == nm:
                variant_names.append( f"{nm}_{m.groups()[1]}")
        return variant_names

    if check or extract:
        with (results_dir / "__hierTree.json").open("rt") as fp:
            order = json.load(fp)
        logger.debug( f"Topological order: {order}")

        assert order[-1] == subckt, f"Last in topological order should be the subckt {subckt} {order}"

        # Process subblocks as well
        for nm in order[:-1]:
            for variant_name in find_variant_names(nm):
                logger.debug(f"variant_name: {variant_name}")
                file_ = results_dir / ( variant_name + ".db.json")
                logger.debug(f"subblock: {file_.name}")
                # Hack: put results in input dir
                _generate_json( file_, variant_name, primitive_dir, pdk_dir, working_dir, check, extract, input_dir=working_dir)

    variants = collections.defaultdict(collections.defaultdict)
    for file_ in results_dir.iterdir():
        variant = file_.name.split('.')[0]
        if not variant.replace(f'{subckt}_', '').isdigit():
            continue
        if file_.suffixes == ['.gds', '.json']:
            variants[variant]['gdsjson'] = file_
        elif file_.suffixes == ['.lef']:
            variants[variant]['lef'] = file_
        elif file_.suffixes == ['.db', '.json'] and (check or extract):
            logger.debug( f".db.json: {file_.name}")
            variants[variant].update(_generate_json(file_, variant, primitive_dir, pdk_dir, working_dir, check, extract, input_dir=working_dir))

    return variants
