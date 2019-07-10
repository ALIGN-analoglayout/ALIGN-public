import json
import sys
import datetime
import pytest

sys.path.append('./Cell_Fabric_FinFET__Mock')

import gen_gds_json
import fabric_NMOS
import pattern_generator

@pytest.fixture
def setup():
    fin_u = 12
    fin = 12
    x_cells = 4
    y_cells = 2
    gate = 2
    gateDummy = 3 ### Total Dummy gates per unit cell: 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell: 2*finDummy
    gu = gate + 2*gateDummy
     ##### Routing
    SDG =(SA, GA, DA, SB, GB, DB) = pattern_generator.pattern.common_centroid(x_cells, gu, gate, gateDummy)

    S = SA+SB
    CcM3 = (min(S)+max(S))//2

    uc = fabric_NMOS.UnitCell( fin_u, fin, finDummy, gate, gateDummy, '../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        Routing = [('S', S, 1, CcM3), ('DA', DA if y%2==0 else DB, 2, CcM3-1), ('DB', DB if y%2==0 else DA, 3, CcM3+1), ('GA', GA if y%2==0 else GB, 4, CcM3-2), ('GB', GB if y%2==0 else GA, 5, CcM3+2)]

        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy, SDG, Routing)

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

def test_fabric_gds_json():


    fn = "tests/__json_dp_nmos"


    with open( fn + "_cand", "rt") as fp0, \
         open(fn + "_gds_cand", 'wt') as fp1:
        gen_gds_json.translate("test", '', fp0, fp1, datetime.datetime( 2019, 1, 1, 0, 0, 0))

    with open( fn + "_gds_cand", "rt") as fp0, \
         open( fn + "_gds_gold", "rt") as fp1:
        cand = json.load( fp0)
        gold = json.load( fp1)
        assert cand == gold


