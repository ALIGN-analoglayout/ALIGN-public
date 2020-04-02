#!/usr/bin/env python

import flow2
import sys

flow2.run_sh( 'rm -f __json')
flow2.run_sh( 'rm -f __json_grs')
flow2.run_sh( 'rm -f $ALIGN_HOME/Viewer/INPUT/comparator_kbc.json')

from intel_p1222p2 import generate_comparator_kbc

generate_comparator_kbc.generate()

cmd = '-sgr -src comparator_kbc -td Intel/DR_COLLATERAL_Generator/22nm --placer_json __json --gr_json __json_grs --no_interface --router_executable $AMSR_EXE'
cmdlist = list(filter( lambda x: x != '', cmd.split( ' ')))

flow2.cmdline( sys.argv[1:] + cmdlist)
