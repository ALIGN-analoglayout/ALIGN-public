import subprocess
import pathlib
import os
import logging
logger = logging.getLogger(__name__)

def generate_pnr(input_dir, lef_file, verilog_file, map_file, pdk_file, design_name, unknownarg1=1, unknownarg2=0):
    assert 'ALIGN_HOME' in os.environ, "ALIGN_HOME not in environment"
    compiler_path = pathlib.Path(os.environ['ALIGN_HOME']).resolve() / 'PlaceRouteHierFlow' / 'pnr_compiler'
    assert compiler_path.is_file(), f"{compiler_path} not found"
    cmd = [str(x) for x in (compiler_path, input_dir, lef_file, verilog_file, map_file, pdk_file, design_name, unknownarg1, unknownarg2)]
    try:
        subprocess.run(cmd, stderr=subprocess.PIPE, check=True)
    except subprocess.CalledProcessError as e:
        logger.critical(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        print(f"\nCall to '{' '.join(cmd)}' failed with error message:\n\n{e.stderr.decode('utf-8')}")
        return None
    return True