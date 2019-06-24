
from cell_fabric import DefaultCanvas, Pdk

import json

import itertools

def test_one():

    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    c = DefaultCanvas(p)
    assert c.generate_routing_collateral( "tests/routing_collateral_cand")
