import fabric_Cap

import math
import json

def test_fabric_Cap():
    unit_cap = 1

    x_cells = 1
    y_cells = 1

    x_length = float((math.sqrt(unit_cap/2))*1000)
    y_length = float((math.sqrt(unit_cap/2))*1000)  

    uc = fabric_Cap.UnitCell()

    uc.unit(0, 0, x_length, y_length, x_cells, y_cells)
    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_cap_small"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data_golden = json.load( fp)

        assert data['bbox'] == data_golden['bbox']
#        assert data == data_golden

        for (x,y) in zip( data['terminals'], data_golden['terminals']):
            x['netName'] = '_'
            y['netName'] = '_'
            assert x == y



def test_fabric_Cap_no_duplicates():
    unit_cap = 1

    x_cells = 1
    y_cells = 1

    x_length = float((math.sqrt(unit_cap/2))*1000)
    y_length = float((math.sqrt(unit_cap/2))*1000)  

    uc = fabric_Cap.UnitCell()

    uc.unit(0, 0, x_length, y_length, x_cells, y_cells)
    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.removeDuplicates()}

    fn = "tests/__json_cap_small_no_duplicates"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data_golden = json.load( fp)

        assert data['bbox'] == data_golden['bbox']
#        assert data == data_golden
        for (x,y) in zip( data['terminals'], data_golden['terminals']):
            x['netName'] = '_'
            y['netName'] = '_'
            assert x == y
