import subprocess
import pathlib
import os
import logging
logger = logging.getLogger(__name__)

def generate_pnr(topology_dir, primitive_dir, pdk_dir, working_dir, subckt, unknownarg1=1, unknownarg2=0):

    # Check to make sure pnr_compiler is available to begin with
    assert 'ALIGN_HOME' in os.environ, "ALIGN_HOME not in environment"
    compiler_path = pathlib.Path(os.environ['ALIGN_HOME']).resolve() / 'PlaceRouteHierFlow' / 'pnr_compiler'
    assert compiler_path.is_file(), f"{compiler_path} not found. Has it been built?"

    # Generate file name inputs
    map_file = f'{subckt}.map'
    lef_file = f'{subckt}.lef'
    verilog_file = f'{subckt}.v'
    pdk_file = 'layers.json'

    # Generate .map & .lef inputs for PnR
    with (working_dir / map_file).open(mode='wt') as mp, \
         (working_dir / lef_file).open(mode='wt') as lp:
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
    (working_dir / verilog_file).write_text((topology_dir / verilog_file).read_text())
    for file_ in topology_dir.iterdir():
        if file_.suffix == '.const':
            (working_dir / file_.name).write_text(file_.read_text())

    # Copy pdk file
    (working_dir / pdk_file).write_text((pdk_dir / pdk_file).read_text())

    # Copy primitive json files
    for file_ in primitive_dir.iterdir():
        if file_.suffix == '.json':
            (working_dir / file_.name).write_text(file_.read_text())

    # Run pnr_compiler
    cmd = [str(x) for x in (compiler_path, working_dir, lef_file, verilog_file, map_file, pdk_file, subckt, unknownarg1, unknownarg2)]
    try:
        subprocess.run(cmd, stderr=subprocess.PIPE, check=True)
    except subprocess.CalledProcessError as e:
        logger.critical(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        print(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        return None
    return True