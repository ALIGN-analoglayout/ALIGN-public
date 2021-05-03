import json
import pathlib
import io
import pytest
import os

from align.pnr.cmdline import cmdline

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
    d = mydir / "current_mirror_ota_inputs"
    argv = [ 'pnr_compiler.py', str(d), f'{nm}.lef', f'{nm}.v', f'{nm}.map', 'layers.json', nm, '1', '0']
    cmdline( argv, results_dir=str(pathlib.Path(ALIGN_WORK_DIR) / 'test_verilog_Results'))

def test_verilog_json():
    nm = 'current_mirror_ota'
    d = mydir / "current_mirror_ota_inputs"
    argv = [ 'pnr_compiler.py', str(d), f'{nm}.lef', f'{nm}.verilog.json', f'{nm}.map', 'layers.json', nm, '1', '0']
    cmdline( argv, results_dir=str(pathlib.Path(ALIGN_WORK_DIR) / 'test_verilog_json_Results'))
