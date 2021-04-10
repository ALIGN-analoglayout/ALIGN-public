import json
import pathlib
import io

from align.pnr import pnr_compiler

mydir = pathlib.Path(__file__).resolve().parent

def test_A():
    
    nm = 'current_mirror_ota'

    d = mydir / "current_mirror_ota_inputs"

    argv = [ 'pnr_compiler.py', str(d), f'{nm}.lef', f'{nm}.v', f'{nm}.map', 'layers.json', nm, '1', '0']

    pnr_compiler.cmdline( argv)
