from fabric_14nm_mock import fabric_Cap

import math
import json

def test_fabric_Cap():
    unit_cap = 10

    x_cells = 1
    y_cells = 1

    x_length = float((math.sqrt(unit_cap/2))*1000)
    y_length = float((math.sqrt(unit_cap/2))*1000)  
    uc = fabric_Cap.UnitCell()

    uc.unit(0, 0, x_length, y_length, x_cells, y_cells)
    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_cap_gold"
    fn2 = "tests/__json_cap_cand"

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
