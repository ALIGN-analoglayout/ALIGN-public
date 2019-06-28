
import json
import pathlib

import re

def import_gds(fp):
    j = json.load( fp)

    
    l23 = j['bgnlib'][0]['bgnstr']

    print( len(l23))

    
    p = re.compile( r'^M(\d+)_M(\d+)_CDNS_(\d+)_(\d+)(|_(\d+))$')

    r23 = [ x for x in l23 if not p.match(x['strname'])]

    def extract( nm):
        return [ x for x in l23 if x['strname'] == nm][0]

    def get_bb( l):
        return [ x for x in l if 'datatype' in x and x['datatype'] == 5]

    def boundary_to_rect( b):
        indices = [0,1,4,3]
        same_pairs = [(0,2), (0,8), (1,9), (3,5), (4,6)]
        assert all( b[i] == b[j] for (i,j) in same_pairs)
        return [ b[i] for i in indices]

    result = []
    for x in r23:
        bb = get_bb(x['elements'])
        result.append( (x['strname'], boundary_to_rect( bb[0]['xy'])))

    return result,r23
