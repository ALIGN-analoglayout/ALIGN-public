import fabric_Cap

import math
import json

from itertools import product

def test_fabric_Cap_big():
    unit_cap = 10

    x_cells = 3
    y_cells = 2

    x_length = float((math.sqrt(unit_cap/2))*1000)
    y_length = float((math.sqrt(unit_cap/2))*1000)  
    uc = fabric_Cap.UnitCell()

    for (x,y) in product( range(x_cells), range(y_cells)):
        uc.unit(x, y, x_length, y_length, x_cells, y_cells)

    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_cap_big_gold"
    fn2 = "tests/__json_cap_big_cand"

    with open( fn2, "wt") as fp2:
        fp2.write( json.dumps( data, indent=2) + '\n')

    if False:
        with open( fn, "wt") as fp:
            fp.write( json.dumps( data, indent=2) + '\n')

    else:
        with open( fn, "rt") as fp:
            data_golden = json.load( fp)

        assert data['bbox'] == data_golden['bbox']
        assert data == data_golden
