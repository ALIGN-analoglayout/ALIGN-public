import pathlib
import json

from pnrdb import *
from cell_fabric import DefaultCanvas, transformation
from pprint import pformat

import pytest
import os

import re


def aux(fn):
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
        'metal6': 'M6',
        'metal7': 'M7',
        'via1': 'V1',
        'via2': 'V2',
        'via3': 'V3',
        'via4': 'V4',
        'via5': 'V5',
        'via6': 'V6',
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

def test_remove_duplicates_telescopic_ota():
    aux("telescopic_ota")

def test_remove_duplicates_five_transistor_ota():
    aux("five_transistor_ota")

def test_remove_duplicates_cascode_current_mirror_ota():
    aux("cascode_current_mirror_ota")

