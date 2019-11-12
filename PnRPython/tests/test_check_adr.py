import pathlib
import json

from pnrdb import *
from cell_fabric import DefaultCanvas, transformation
from pprint import pformat

import pytest
import os

import re

def test_remove_duplicates():
#    fn = "telescopic_ota"
    fn = "five_transistor_ota"
    fpath = pathlib.Path( f"tests/{fn}_adr_dr_globalrouting.json")
    with fpath.open( "rt") as fp:
        d = json.load( fp)
        
    pdk = "../PDK_Abstraction/FinFET14nm_Mock_PDK"
    sys.path.append(str(pathlib.Path(pdk).parent.resolve()))
    pdkpkg = pathlib.Path(pdk).name
    canvas = importlib.import_module(f'{pdkpkg}.canvas')
    # TODO: Remove these hardcoded widths & heights from __init__()
    #       (Height may be okay since it defines UnitCellHeight)
    cnv = getattr(canvas, f'{pdkpkg}_Canvas')(12, 4, 2, 3)


    layer_map = {
        'metal1': 'M1',
        'metal2': 'M2',
        'metal3': 'M3',
        'metal4': 'M4',
        'metal5': 'M5',
        'via1': 'V1',
        'via2': 'V2',
        'via3': 'V3',
        'via4': 'V4'
    }

    p_exclude = re.compile( '^((.*_gr)|(!kor))$')

    terminals = []
    for term in d["terminals"]:
        # crazy hack to remove two different via sizes
        if term['layer'] == 'V2':
            r = term['rect']
            if r[2]-r[0] == 320: # make it be 400
                r[0] -= 40
                r[2] += 40
            term['rect'] = r

        if term['layer'] in layer_map:
            term['layer'] = layer_map[term['layer']]
            if not p_exclude.match( term['netName']):
                terminals.append(term)
    d["terminals"] = terminals

    rational_scaling( d, div=5)

    cnv.bbox = transformation.Rect( *d["bbox"])
    cnv.terminals = d["terminals"]

#
# We need to merge in the leaf cells
#

    cnv.gen_data(run_pex=False)

    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    assert len(cnv.rd.opens) == 0, pformat(cnv.rd.opens)
    assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
