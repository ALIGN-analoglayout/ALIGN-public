import json
import pathlib

from align.pnr import *
from pprint import pformat

mydir = pathlib.Path(__file__).resolve().parent

def get_hN(fn):
    with open(fn,"rt") as fp:
        hN = hierNode(json.load(fp))
        return hN

def test_gen_viewer_json():
    hN = get_hN(mydir / "telescopic_ota-freeze.json")
    d = gen_viewer_json( hN)

    with open(mydir / "telescopic_ota_dr_globalrouting.json","wt") as fp:
        json.dump( d, fp=fp, indent=2)


def test_gen_viewer_json2():
    hN = get_hN(mydir / "switched_capacitor_filter-freeze.json")
    d = gen_viewer_json( hN)

    with open(mydir / "switched_capacitor_filter_dr_globalrouting.json","wt") as fp:
        json.dump( d, fp=fp, indent=2)

def test_gen_viewer_json3():
    hN = get_hN(mydir / "switched_capacitor_combination-freeze.json")

    d = gen_viewer_json( hN)

    with open(mydir / "switched_capacitor_combination_dr_globalrouting.json","wt") as fp:
        json.dump( d, fp=fp, indent=2)


def test_remove_duplicates():
    hN = get_hN(mydir / "telescopic_ota-freeze.json")
    cnv, _ = gen_viewer_json( hN, checkOnly=True)
    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    # assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)

def test_remove_duplicates2():
    hN = get_hN(mydir / "switched_capacitor_filter-freeze.json")
    cnv, _ = gen_viewer_json( hN, checkOnly=True)
    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    # assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)

def test_remove_duplicates3():
    hN = get_hN(mydir / "switched_capacitor_combination-freeze.json")
    cnv, _ = gen_viewer_json( hN, checkOnly=True)
    assert len(cnv.rd.different_widths) == 0, pformat(cnv.rd.different_widths)
    assert len(cnv.rd.shorts) == 0, pformat(cnv.rd.shorts)
    # assert len(cnv.drc.errors) == 0, pformat(cnv.drc.errors)
