import subprocess
import pathlib
import os
import logging
import collections
import json

from .db import hierNode
from .checkers import gen_viewer_json

logger = logging.getLogger(__name__)

def _generate_json(dbfile, variant, primitive_dir, pdk_dir, output_dir, check=False, extract=False):

    ret = {}
    with open(dbfile,"rt") as fp:
        hN = hierNode(json.load(fp))
    res = gen_viewer_json( hN, pdk=pdk_dir, draw_grid=True, json_dir=str(primitive_dir), checkOnly=(check or extract), extract=extract)

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
            print("found files",file_)
            if file_.suffixes == ['.gds', '.json']:
                true_stem = file_.stem.split('.')[0]
                mp.write(f'{true_stem} {true_stem}.gds\n')
            elif file_.suffix == '.lef' and file_.stem != subckt:
                print("found lef files",file_)
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
        subprocess.run(cmd, stderr=subprocess.PIPE, check=True, cwd=working_dir)
    except subprocess.CalledProcessError as e:
        logger.critical(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        print(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        return {}

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
            variants[variant].update(_generate_json(file_, variant, primitive_dir, pdk_dir, working_dir, check, extract))

    return variants
