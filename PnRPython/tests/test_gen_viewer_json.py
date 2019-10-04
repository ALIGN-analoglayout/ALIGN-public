import json

from pnrdb import *
from cell_fabric import DefaultCanvas, Pdk, transformation
from pprint import pformat

def get_hN(fn="tests/telescopic_ota-freeze.json"):
    with open(fn,"rt") as fp:
        hN = hierNode(json.load(fp))
        return hN

def test_gen_viewer_json():
    hN = get_hN()
    d = gen_viewer_json( hN)

    with open("telescopic_ota_dr_globalrouting.json","wt") as fp:
        json.dump( d, fp=fp, indent=2)


def test_gen_viewer_json2():
    hN = get_hN("tests/switched_capacitor_filter-freeze.json")
    d = gen_viewer_json( hN)

    with open("switched_capacitor_filter_dr_globalrouting.json","wt") as fp:
        json.dump( d, fp=fp, indent=2)

def test_gen_viewer_json3():
    hN = get_hN("tests/switched_capacitor_combination-freeze.json")

    d = gen_viewer_json( hN)

    with open("switched_capacitor_combination_dr_globalrouting.json","wt") as fp:
        json.dump( d, fp=fp, indent=2)


def test_remove_duplicates():
    hN = get_hN()
    cnv = gen_viewer_json( hN, checkOnly=True)
    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    # assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)

def test_remove_duplicates2():
    hN = get_hN("tests/switched_capacitor_filter-freeze.json")
    cnv = gen_viewer_json( hN, checkOnly=True)
    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    # assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)

def test_remove_duplicates3():
    hN = get_hN("tests/switched_capacitor_combination-freeze.json")
    cnv = gen_viewer_json( hN, checkOnly=True)
    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    # assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
