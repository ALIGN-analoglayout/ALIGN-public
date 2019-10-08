import json
import sys
import datetime
import pytest
import pathlib

pdkpath = '../PDK_Abstraction/FinFET14nm_Mock_PDK'
sys.path.append(pdkpath)

import gen_gds_json
import primitive

@pytest.fixture
def setup():
    fin = 12
    x_cells = 4
    y_cells = 2
    gate = 2
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy

    uc = primitive.PrimitiveGenerator( fin, finDummy, gate, gateDummy, (pathlib.Path(pdkpath) / 'layers.json').resolve() )

    Routing = {'S':  [('M1', 'S'), ('M2', 'S')],
               'DA': [('M1', 'D')],
               'DB': [('M2', 'D')],
               'GA': [('M1', 'G')],
               'GB': [('M2', 'G')]}

    uc.addNMOSArray( x_cells, y_cells, 1, Routing)

    return uc

def test_fabric_Dp(setup):

    uc = setup

    fn = "tests/__json_dp_nmos"

    with open( fn + "_cand", "wt") as fp:
        uc.writeJSON( fp)

    # Re-opening file to take care of JSON tuple to list conversion
    with open( fn + "_cand", "rt") as fp0, \
         open( fn + "_gold", "rt") as fp1:
        cand = json.load( fp0)
        gold = json.load( fp1)
        assert cand['bbox'] == gold['bbox']
        assert cand == gold

def test_fabric_gds_json(setup):

    uc = setup

    fn = "tests/__json_dp_nmos"

    with open( fn + "_cand", "rt") as fp0, \
         open(fn + "_gds_cand", 'wt') as fp1:
        gen_gds_json.translate("test", '', fp0, fp1, datetime.datetime( 2019, 1, 1, 0, 0, 0), uc.pdk)

    with open( fn + "_gds_cand", "rt") as fp0, \
         open( fn + "_gds_gold", "rt") as fp1:
        cand = json.load( fp0)
        gold = json.load( fp1)
        assert cand == gold


def test_fabric_pex(setup):

    c = setup

    c.gen_data()

    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert len(c.rd.subinsts) == 2, c.rd.subinsts

    fn = 'tests/__dp_nmos.cir'

    with open( fn + '_cand', "wt") as fp:

        fp.write("* Extracted network below *\n")
        c.pex.writePex(fp)

        fp.write("\n* Stamping out all devices *\n")
        for instance, v in c.rd.subinsts.items():
            fp.write(f'{instance} NMOS ' + ' '.join( [f'{instance}_{pin}' for pin in v.keys()] ) + '\n' )

        toprint = ['GA_M3_1360_1212', 'GB_M3_1440_1296', 'S_M3_1120_960', 'DA_M3_1200_1044', 'DB_M3_1280_1128']

        fp.write("\n.op")
        fp.write("\n.print dc " + " ".join(toprint))
        fp.write("\n.end")

    with open( fn + "_cand", "rt") as fp0, \
         open( fn + "_gold", "rt") as fp1:
        cand = fp0.read()
        gold = fp1.read()
        assert cand == gold
