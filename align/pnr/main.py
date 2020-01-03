import subprocess
import pathlib
import os
import logging

from ..gdsconv.json2gds import convert_GDSjson_GDS

logger = logging.getLogger(__name__)

def generate_pnr(topology_dir, primitive_dir, pdk_dir, output_dir, subckt, variants=1, effort=0, save_state=False):

    # Check to make sure pnr_compiler is available to begin with
    assert 'ALIGN_HOME' in os.environ, "ALIGN_HOME not in environment"
    compiler_path = pathlib.Path(os.environ['ALIGN_HOME']).resolve() / 'PlaceRouteHierFlow' / 'pnr_compiler'
    assert compiler_path.is_file(), f"{compiler_path} not found. Has it been built?"

    # Create working & input directories
    working_dir = output_dir / 'workspace'
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
            if file_.suffixes == ['.gds', '.json']:
                true_stem = file_.stem.split('.')[0]
                mp.write(f'{true_stem} {true_stem}.gds\n')
            elif file_.suffix == '.lef' and file_.stem != subckt:
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
    if save_state:
        os.environ['PNRDB_SAVE_STATE'] = ''

    # Run pnr_compiler
    cmd = [str(x) for x in (compiler_path, input_dir, lef_file, verilog_file, map_file, pdk_file, subckt, variants, effort)]
    try:
        subprocess.run(cmd, stderr=subprocess.PIPE, check=True, cwd=working_dir)
    except subprocess.CalledProcessError as e:
        logger.critical(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        print(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        return {}

    convert_GDSjson_GDS(results_dir / f'{subckt}_0.gds.json', output_dir / f'{subckt}_0.gds')

    return True