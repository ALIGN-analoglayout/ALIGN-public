#!/usr/bin/env python

import flow2
import sys
import importlib

name = sys.argv[1]

flow2.run_sh( 'rm -f __json')
flow2.run_sh( 'rm -f __json_grs')
flow2.run_sh( f'rm -f $ALIGN_HOME/Viewer/INPUT/{name}.json')

g = importlib.import_module( f'intel_p1222p2.generate_{name}')

g.generate()

cmd = f'-sgr -src {name} -td Intel/DR_COLLATERAL_Generator/22nm --placer_json __json --gr_json __json_grs --no_interface --router_executable $AMSR_EXE'
cmdlist = list(filter( lambda x: x != '', cmd.split( ' ')))

flow2.cmdline( sys.argv[2:] + cmdlist)