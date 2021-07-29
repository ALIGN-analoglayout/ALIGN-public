import pytest
import pathlib
import json

from align.primitive.default import DefaultCanvas
from align.cell_fabric import Pdk

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = DefaultCanvas(p)
    return c

def test_multi_via_postprocessor_v12(setup):
    c = setup
    c.addWire( c.m12, 'a', 2, (1,-1), (13,1))
    c.addWire( c.m13, None, 1, (1,-1), (3,1))
    c.addVia(c.v12, None, 1, 2)

    fn = '__json_multi_via_postprocessor_v12'

    with open( mydir / (fn + "_cand"), "wt") as fp:
        data = c.writeJSON(fp, postprocess=True)

    with open( mydir / (fn + "_gold"), "rt") as fp:
        data2 = json.load( fp)

    assert data == data2
