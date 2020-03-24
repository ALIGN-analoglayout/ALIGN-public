#!/usr/bin/env python

import sys
import importlib
import os
import pathlib
import stat
import json
import re
from align.cell_fabric import transformation
from intel_p1222p2.IntelP1222p2Canvas import IntelP1222p2Canvas


def import_result(name):

    if not name.endswith('.json'):
        name += '.json'

    with open( name, "rt") as fp:
        d = json.load(fp)

    layer_tbl = { 
                  "tcn": "Diffcon",
                  "gcn": "Polycon",
                  "diffcon": "Diffcon",
                  "polycon": "Polycon",
                  "nwell": "Nwell",
                  "ndiff": "Ndiff",
                  "pdiff": "Pdiff",
                  "metal1": "M1",
                  "metal2": "M2",
                  "metal3": "M3",
                  "metal4": "M4",
                  "metal5": "M5",
                  "via0": "V0",
                  "via1": "V1",
                  "via2": "V2",
                  "via3": "V3",
                  "via4": "V4"}

    p = re.compile( "^(.*)_gr$")

    def s( r):
        assert all( v%10 == 0 for v in r)
        return [ v//10 for v in r]

    terminals = []
    for term in d['terminals']:
        ly = term['layer']
        nm = term['netName'] if 'netName' in term else term['net_name']
        if nm is not None and p.match(nm): continue
        term['layer'] = layer_tbl.get( ly, ly)
        term['rect'] = s(term['rect'])
        # SY: Remove net_name from boundary terminals for improve viewing
        if str(term['layer']).lower() == 'boundary': 
            net_name = 'netName' if 'netName' in term else 'net_name'
            term[net_name] = None
        terminals.append( term)
    d['terminals'] = terminals

    cnv = IntelP1222p2Canvas()
    cnv.bbox = transformation.Rect( *s(d['bbox']))
    cnv.terminals = d['terminals']
    return(cnv)


def main( name, generate=False, args=None):

    if args is None: args = []

    assert 'ALIGN_HOME' in os.environ
    ALIGN_HOME = os.environ['ALIGN_HOME']

    spec = importlib.util.spec_from_file_location("flow", f'{ALIGN_HOME}/Cktgen/flow.py')
    flow = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(flow)

    flow.run_sh( 'rm -rf INPUT')

    if generate:
        flow.run_sh( 'rm -f __json')
        flow.run_sh( 'rm -f __json_grs')
        flow.run_sh( f'rm -f $ALIGN_HOME/Viewer/INPUT/{name}.json')
        g = importlib.import_module( f'intel_p1222p2.generate_{name}')
        g.generate()

    td = '/dataVolume/git/analog-placer-22nm/DR_COLLATERAL_Generator/22nm'

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

    return( import_result( name))


if __name__ == "__main__":
    main( sys.argv[1], generate=True, args=sys.argv[2:])
    pass
