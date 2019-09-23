import json
import sys
import datetime
import pytest

sys.path.append('./Cell_Fabric_FinFET__Mock')

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

    uc = primitive.PrimitiveGenerator( fin, finDummy, gate, gateDummy, '../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')

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
        data = uc.writeJSON( fp)

    with open( fn + "_gold", "rt") as fp:
        data_golden = json.load( fp)
        assert data['bbox'] == data_golden['bbox']
        assert data == data_golden

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

    fn = 'tests/_dp_nmos.cir'

    with open( fn + '_cand', "wt") as fp:

        fp.write("* Extracted network below *\n")
        c.pex.writePex(fp)

        fp.write("\n* Grounding all V0 nodes *\n")
        for i, sink in enumerate(sorted(\
                {comp[1] for comp in c.pex.components if comp[1] != 0 and comp[1].startswith('v0_None')},\
                key = lambda x: tuple([int(n) if n.isdigit() else n for n in x.split('_')]))):
            fp.write(f"V{i} {sink} 0 0\n")

        toprint = []
        fp.write("\n* Adding current sources to all M2 nodes *\n")
        for i, source in enumerate(sorted(\
                {net for comp in c.pex.components for net in comp[1:2] if 'M2' in net},\
                key = lambda x: tuple([int(n) if n.isdigit() else n for n in x.split('_')]))):
            fp.write(f"I{i} {source} 0 1\n")
            toprint.append(f"V({source})")

        fp.write("\n.op")
        fp.write("\n.print dc " + " ".join(toprint))
        fp.write("\n.end")
