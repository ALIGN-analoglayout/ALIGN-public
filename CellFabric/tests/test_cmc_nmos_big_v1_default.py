import fabric_CMC_NMOS_v1_default

import math
import json

import itertools

def test_fabric_Cap1():

    x_cells = 4	
    y_cells = 2
    fin_u = 12
    #gate_u = int(sys.argv[4])
    gate = 2
    fin = 2*((fin_u+1)//2)
    gateDummy = 3 ### Total Dummy gates per unit cell 2*gateDummy
    finDummy = 4  ### Total Dummy fins per unit cell 2*finDummy

    uc = fabric_CMC_NMOS_v1_default.UnitCell( fin_u, fin, finDummy, gate, gateDummy)

    for (x,y) in ( (x,y) for x in range(x_cells) for y in range(y_cells)):
        uc.unit( x, y, x_cells, y_cells, fin_u, fin, finDummy, gate, gateDummy)

    uc.computeBbox()

    data = { 'bbox' : uc.bbox.toList(), 'globalRoutes' : [], 'globalRouteGrid' : [], 'terminals' : uc.terminals}

    fn = "tests/__json_cmc_nmos_big_v1_default"

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
