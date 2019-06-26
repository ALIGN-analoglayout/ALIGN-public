import fabric_default

import json

import itertools

def test_fabric_default():
    unit_cap = 10

    fin_u1 = 8
    x_cells = 2
    y_cells = 1

    gate_u = 2
    if fin_u1%2 != 0:
        fin_u = fin_u1 + 1
    else:
        fin_u = fin_u1 

    uc = fabric_default.UnitCell( gate_u, fin_u, fin_u1)

    for (x,y) in itertools.product( range(x_cells), range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, gate_u)

    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_default_fabric_nmos"

    with open( fn + "_cand", "wt") as fp:
        fp.write( json.dumps( data, indent=2) + '\n')

    with open( fn + "_gold", "rt") as fp:
        data_golden = json.load( fp)
        assert data['bbox'] == data_golden['bbox']
#        assert data == data_golden
        for (x,y) in zip( data['terminals'], data_golden['terminals']):
            x['netName'] = '_'
            y['netName'] = '_'
            x['pin'] = '_'
            y['pin'] = '_'
            assert x == y
