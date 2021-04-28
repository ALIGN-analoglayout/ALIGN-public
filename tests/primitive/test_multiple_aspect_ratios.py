import pytest
import align
import os
import pathlib
import json
import re
import logging
from collections import defaultdict

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

def test_primitive_multiple_aspect_ratios():
    design_dir = ALIGN_HOME / 'examples' / 'current_mirror_ota'

    current = pathlib.Path(__file__).resolve().parent
    run_dir = current / 'current_mirror_ota'

    with (run_dir / '1_topology' / 'current_mirror_ota.verilog.json').open('rt') as fp:
        verilog_d = json.load(fp)

    with (run_dir / '1_topology' / 'primitives.json').open('rt') as fp:
        primitives_d = json.load(fp)

    map_d = defaultdict(list)

    p = re.compile( r'^(\S+)_nfin(\d+)_n(\d+)_X(\d+)_Y(\d+)_(\S+)$')
    for k,v in primitives_d.items():
        m = p.match(k)
        if m:
            nfin,n,X,Y = tuple(int(x) for x in m.groups()[1:5])
            abstract_name = f'{m.groups()[0]}_nfin{nfin}_{m.groups()[5]}'
            map_d[abstract_name].append( k)
        else:
            print( f'No match for primitive {k}')

    concrete2abstract = { vv:k for k,v in map_d.items() for vv in v}

    map2_d = []
    for k,v in map_d.items():
        map2_d.append( {'abstract_template_name': k, 'concrete_template_names': v})
    print(json.dumps( map2_d, indent=2))

    args = [str(design_dir), '-c', '--flow_start', '2_primitives', '--flow_stop', '2_primitives']

    os.chdir( run_dir)

    results = align.CmdlineParser().parse_args(args)

