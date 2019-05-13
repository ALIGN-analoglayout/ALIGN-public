import fabric_CMC_NMOS

import math
import json

import itertools

def test_fabric_Cap():
    unit_cap = 10

    fin_u1 = 8
    x_cells = 2
    y_cells = 1

    gate_u = 2
    if fin_u1%2 != 0:
        fin_u = fin_u1 + 1
    else:
        fin_u = fin_u1 

    uc = fabric_CMC_NMOS.UnitCell( gate_u, fin_u, fin_u1)

    for (x,y) in itertools.product( range(x_cells), range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, gate_u)

    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_cmc_nmos_gold"
    fn2 = "tests/__json_cmc_nmos_cand"

    with open( fn2, "wt") as fp2:
        fp2.write( json.dumps( data, indent=2) + '\n')

    with open( fn, "rt") as fp:
        data_golden = json.load( fp)
        assert data['bbox'] == data_golden['bbox']
        assert data == data_golden
