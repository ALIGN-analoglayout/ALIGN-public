import pytest
import itertools
import math
import filecmp
import pathlib

from align.primitive.default import DefaultCanvas
from align.cell_fabric import Pdk

mydir = pathlib.Path(__file__).resolve().parent
pdkfile = mydir.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK' / 'layers.json'

@pytest.fixture
def setup():
    p = Pdk().load(pdkfile)
    c = DefaultCanvas(p)
    return c

def test_m1_pex(setup):
    c = setup
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300], 'netType': 'drawing'}]
    c.gen_data()
    assert len(c.pex.netCells) == math.ceil(300 / c.pdk['Poly']['Pitch'])

def test_m2_pex(setup):
    c = setup
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [0, 0, 300, 100], 'netType': 'drawing'}]
    c.gen_data()
    assert len(c.pex.netCells) == math.ceil(300 / c.pdk['Poly']['Pitch'])

def test_via_pex(setup):
    c = setup
    for (i,nm) in itertools.chain( itertools.product( [0,2,4], ['a']), itertools.product( [1,3,5], ['b'])):
        c.addWire( c.m1, nm, None, i, (0,-1), (3,-1))
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +=======+=======*
                    b
+a======+=======+   |
                    |
    +=======+=======/
""")

    c.gen_data()

    fn = "__sp_via_set_m2_m3_sticks"

    with open( mydir / (fn + "_cand"), "wt") as fp:
        c.pex.writePex(fp)

    assert filecmp.cmp(mydir / (fn + "_cand"), mydir / (fn + "_gold"))

def test_via_pex2(setup):
    c = setup
    for (i,nm) in itertools.product( [5,7,9], ['a']):
        c.addWire( c.m1, nm, None, i, (0,-1), (0,1))
    for (i,nm) in itertools.product( [1,3,5,7,9], ['a']):
        c.addWire( c.m1, nm, None, i, (4,-1), (4,1))
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +=======+=======*=======+=======+
                    a
                    |
                    |
                    |
                    |
                    |
                    |
                    *=======+=======+
""")

    c.gen_data()

    fn = "Foo.cir"

    source = f"a_M1_{80*1}_{84*4}"
    sink1  = f"a_M1_{80*9}_{84*4}"
    sink2  = f"a_M1_{80*9}_{84*0}"

    hack0 = "{2*period-slew}"
    hack1 = "PULSE(0 {vcc_value} 0ps {slew} {slew} {data_on} {period*4})"

    with open( mydir / fn, "wt") as fp:
        fp.write(f"""* PEX
.param vcc_value=1
.param slew=1fs
.param period=100fs
.param data_on={hack0}

V1 {source} 0 {hack1}

""")
        c.pex.writePex(fp)
        fp.write(f"""
.tran 0 400f 0 0.01f
.print tran V({source}) V({sink1}) V({sink2})
.end
""")

    assert filecmp.cmp(mydir / fn, mydir / (fn + "-gold"))

def test_via_pex_current(setup):
    c = setup
    for (i,nm) in itertools.product( [5,7,9], ['a']):
        c.addWire( c.m1, nm, None, i, (0,-1), (0,1))
    for (i,nm) in itertools.product( [1,3,5,7,9], ['a']):
        c.addWire( c.m1, nm, None, i, (4,-1), (4,1))
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +=======+=======*=======+=======+
                    a
                    |
                    |
                    |
                    |
                    |
                    |
                    *=======+=======+
""")

    c.gen_data()

    fn = "Foo2.cir"

    source = f"a_M1_{80*1}_{84*4}"
    sink1  = f"a_M1_{80*9}_{84*4}"
    sink2  = f"a_M1_{80*9}_{84*0}"

    internal1 = f"a_M1_{80*5}_{84*4}"
    internal2 = f"a_M1_{80*5}_{84*0}"

    with open( mydir / fn, "wt") as fp:
        fp.write(f"""* PEX

I0 {source} 0 10u
V1 {sink1} 0 0
V2 {sink2} 0 0

""")
        c.pex.writePex(fp)
        fp.write(f"""
.op
.print dc V({source}) I(V1) I(V2) V({internal1}) V({internal2})
.end
""")

    assert filecmp.cmp(mydir / fn, mydir / (fn + "-gold"))

def test_via_pex_current2(setup):
    c = setup
    for (i,nm) in itertools.product( [5,7,9], ['a']):
        c.addWire( c.m1, nm, None, i, (0,-1), (0,1))
    for (i,nm) in itertools.product( [5,7,9], ['a']):
        c.addWire( c.m1, nm, None, i, (4,-1), (4,1))
    for (i,nm) in itertools.product( [1,3], ['a']):
        c.addWire( c.m1, nm, None, i, (2,-1), (2,1))
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
                    *=======+=======+
                    a
                    |
                    |
    +=======+=======/
                    |
                    |
                    |
                    *=======+=======+
""")

    c.gen_data()

    fn = "Foo3.cir"

    source = f"a_M1_{80*1}_{84*2}"
    sink1  = f"a_M1_{80*9}_{84*4}"
    sink2  = f"a_M1_{80*9}_{84*0}"

    internal1 = f"a_M1_{80*5}_{84*4}"
    internal2 = f"a_M1_{80*5}_{84*0}"

    with open( mydir / fn, "wt") as fp:
        fp.write(f"""* PEX

I0 {source} 0 10u
V1 {sink1} 0 0
V2 {sink2} 0 0

""")
        c.pex.writePex(fp)
        fp.write(f"""
.op
.print dc V({source}) I(V1) I(V2) V({internal1}) V({internal2})
.end
""")

    assert filecmp.cmp(mydir / fn, mydir / (fn + "-gold"))
