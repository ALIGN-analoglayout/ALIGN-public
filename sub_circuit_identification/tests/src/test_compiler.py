import os
import shutil
import pathlib
from os.path import dirname, abspath, join , isfile
import sys
# Find code directory relative to our directory
THIS_DIR = dirname(__file__)
CODE_DIR = abspath(join(THIS_DIR, '../../', 'src'))
sys.path.append(CODE_DIR)

from compiler import compiler, compiler_output

def test_compiler():
    test_path=(pathlib.Path(__file__).parent / 'ota.sp').resolve()
    updated_ckt = compiler(test_path, "ota",0 )
    all_subckt_list = [ele["name"] for ele in updated_ckt]
    assert 'CMC_PMOS_S' in all_subckt_list
    assert 'CMC_PMOS' in all_subckt_list
    assert 'SCM_NMOS' in all_subckt_list
    assert 'CMC_NMOS' in all_subckt_list
    assert 'DP_NMOS' in all_subckt_list
    assert 'ota' in all_subckt_list

    return(updated_ckt)

def test_compiler_output():
    updated_ckt=test_compiler()
    # Every example should contain a setup file
    test_path=(pathlib.Path(__file__).parent / 'ota.sp').resolve()
    compiler_output(test_path,updated_ckt, 'ota',12 , 12 )
    for files in os.listdir('./'):
        if isfile(files):
            if 'ota' in files or 'const' in files: 
                os.remove(files)
