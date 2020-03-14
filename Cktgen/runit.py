#!/usr/bin/env python

import flow
import sys
import importlib
import os
import pathlib
import stat

name = sys.argv[1]

flow.run_sh( 'rm -f __json')
flow.run_sh( 'rm -f __json_grs')
flow.run_sh( f'rm -f $ALIGN_HOME/Viewer/INPUT/{name}.json')

g = importlib.import_module( f'intel_p1222p2.generate_{name}')

g.generate()

cmd = f'-sgr -src {name} -td Intel/DR_COLLATERAL_Generator/22nm --placer_json __json --gr_json __json_grs --no_interface'

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

flow.cmdline( sys.argv[2:] + cmdlist)
