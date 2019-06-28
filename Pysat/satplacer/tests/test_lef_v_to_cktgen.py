
from satplacer.lef_v_to_cktgen import *
import pytest

import json


def test_vga():
    with open( 'tests/merged.lef', 'rt') as fp:
        lef_str = fp.read()

    with open( 'tests/vga.v', 'rt') as fp:
        verilog_str = fp.read()

    with open( 'tests/vga.pl', 'rt') as fp:
        pl_str = fp.read()

    d = convert( lef_str, verilog_str, pl_str)

    inst_map = { x['instance_name'] : x for x in d['instances'] }

    if False:
# trim to two instances
        d['instances'] = [
                           inst_map["R0"],
                           inst_map["R1"],
                           inst_map["C1"],
                           inst_map["C2"],
                           inst_map["Nsw0"],
                           inst_map["Nsw1"],
                           inst_map["Nsw2"],
                           inst_map["xM03|MN0_xM02|MN0_xM32|MN0_xM12|MN0_xM22|MN0"],
                           inst_map["xM20|MN0_xM21|MN0"],
                           inst_map["xM30|MN0_xM31|MN0"],
                           inst_map["xM10|MN0_xM11|MN0"],
                           inst_map["xM00|MN0_xM01|MN0"]
                         ]


# Hack because the router needs more space on edge
    inst_map['R1']['transformation']['oX'] -= 840


    with open("tests/__json_cktgen_physical_vga", "wt") as fp:
       json.dump( d, indent=2, fp=fp)
       
