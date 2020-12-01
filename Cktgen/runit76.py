#!/usr/bin/env python

import sys
import importlib
import os
import pathlib
import stat
import json
import re
from align.cell_fabric import transformation


def main( name, generate=False, args=None):

    if args is None: args = []

    assert 'ALIGN_HOME' in os.environ
    ALIGN_HOME = os.environ['ALIGN_HOME']
    PDK_HOME = os.environ['PDK_HOME']

    spec = importlib.util.spec_from_file_location("flow", f'{ALIGN_HOME}/Cktgen/flow.py')
    flow = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(flow)

    flow.run_sh( 'rm -rf INPUT')

    if generate:
        flow.run_sh( 'rm -f __json')
        flow.run_sh( 'rm -f __json_grs')
        flow.run_sh( f'rm -f $ALIGN_HOME/Viewer/INPUT/{name}.json')
        g = importlib.import_module( f'intel_p1276p31.generate_{name}')
        g.generate()

    td = f'{PDK_HOME}/intel_p1276p31/DR_COLLATERAL'

    cmd = f'-sgr -src {name} -td {td} --placer_json __json --gr_json __json_grs --no_interface'

    #
    # There are two ways to set a router executable. Set the environment variable,
    # or include '--router_executable /path/to/executable' on the command line
    #
    ev = 'AMSR_EXE'
    if ev in os.environ:
        exe = os.environ[ev]
        assert exe != ''
        p_exe = pathlib.Path(exe)
        assert p_exe.exists() and p_exe.is_file()
        # check if it is intended to be executable
        mask = stat.S_IXUSR | stat.S_IXGRP | stat.S_IXOTH
        mode = p_exe.stat().st_mode
        assert mode & mask != 0, f'Permissions for {exe}: {stat.filemode(mode)}'
        cmd += f' --router_executable {exe}'

    cmdlist = list(filter( lambda x: x != '', cmd.split( ' ')))

    flow.cmdline( args + cmdlist)
    return


if __name__ == "__main__":
    main( sys.argv[1], generate=True, args=sys.argv[2:])
    
