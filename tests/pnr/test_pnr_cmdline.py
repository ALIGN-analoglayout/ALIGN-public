import json
import pathlib
import io
import pytest
import os
import shutil
from align.compiler.write_verilog_lef import write_verilog

from align.pnr.cmdline import cmdline
import align

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

if 'ALIGN_WORK_DIR' in os.environ:
    ALIGN_WORK_DIR = pathlib.Path( os.environ['ALIGN_WORK_DIR']).resolve() 
else:
    ALIGN_WORK_DIR = ALIGN_HOME / 'tests' / 'tmp'

mydir = pathlib.Path(__file__).resolve().parent

def test_verilog():
    nm = 'current_mirror_ota'

    run_dir = ALIGN_WORK_DIR / f'{nm}_pnr_cmdline'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)
    os.chdir(run_dir)

    nm = 'current_mirror_ota'

    design_dir = ALIGN_HOME / 'examples' / nm
    args = [str(design_dir), '--flow_stop', '3_pnr:prep']
    results = align.CmdlineParser().parse_args(args)

    with (run_dir / '3_pnr' / 'inputs' / f"{nm}.verilog.json").open("rt") as fp:
        j = json.load( fp)

    with (run_dir / '3_pnr' / 'inputs' / f"{nm}.v").open("wt") as fp:
        write_verilog( j, fp)

    os.chdir(run_dir / "3_pnr")

    d = "inputs"
    argv = [ 'pnr_compiler.py', "inputs", f'{nm}.lef', f'{nm}.v', f'{nm}.map', 'layers.json', nm, '1', '0']
    cmdline( argv, results_dir='Results')

def test_verilog_json():
    nm = 'current_mirror_ota'

    run_dir = ALIGN_WORK_DIR / f'{nm}_pnr_cmdline'

    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)

    run_dir.mkdir(parents=True, exist_ok=False)
    os.chdir(run_dir)

    design_dir = ALIGN_HOME / 'examples' / nm
    args = [str(design_dir), '--flow_stop', '3_pnr:prep']
    results = align.CmdlineParser().parse_args(args)

    os.chdir(run_dir / "3_pnr")

    d = "inputs"
    argv = [ 'pnr_compiler.py', "inputs", f'{nm}.lef', f'{nm}.verilog.json', f'{nm}.map', 'layers.json', nm, '1', '0']
    cmdline( argv, results_dir='Results')
