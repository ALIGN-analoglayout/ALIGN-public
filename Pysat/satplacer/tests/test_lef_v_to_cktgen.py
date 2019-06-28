
from satplacer.lef_v_to_cktgen import *

import json


def test_two():
    with open( 'tests/merged.lef', 'rt') as fp:
        lef_str = fp.read()

    with open( 'tests/vga.v', 'rt') as fp:
        verilog_str = fp.read()

    with open( 'tests/vga.pl', 'rt') as fp:
        pl_str = fp.read()

    d = convert( lef_str, verilog_str, pl_str)

    if False:
        assert d['nm'] == 'vga'
        assert d['instances'][0]['instance_name'] == 'u0'
        assert len(d['instances'][0]['formal_actual_map']) == 4
        assert d['leaves'][0]['bbox'][0] == 0
        assert d['leaves'][0]['bbox'][1] == 0
        assert d['leaves'][0]['bbox'][2] == 38400
        assert d['leaves'][0]['bbox'][3] == 34440

    with open("tests/__json_cktgen_physical_vga", "wt") as fp:
       json.dump( d, indent=2, fp=fp)
