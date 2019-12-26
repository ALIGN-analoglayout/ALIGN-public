import json
import pathlib

from align.pnr import hierNode, PnRDBEncoder

import io
import copy

mydir = pathlib.Path(__file__).resolve().parent

def test_A():
    with open(mydir / "telescopic_ota-freeze.json","rt") as fp:
        j = json.load(fp)
        hN = hierNode(j)

    with io.StringIO() as fp:
        json.dump( hN, fp=fp, cls=PnRDBEncoder, indent=2)
        s = fp.getvalue()

    with io.StringIO(s) as fp:
        jj = json.load(fp)

    assert j == jj

def test_write():
    with open(mydir / "telescopic_ota-freeze.json","rt") as fp:
        j = json.load(fp)
        j_copy = copy.deepcopy(j)
        hN = hierNode(j)

    assert j['name'] == "telescopic_ota"

    hN.name = "treefrog"

    assert hN.name == "treefrog"

    with io.StringIO() as fp:
        json.dump( hN, fp=fp, cls=PnRDBEncoder, indent=2)
        s = fp.getvalue()

    with io.StringIO(s) as fp:
        jj = json.load(fp)

    assert jj['name'] == "treefrog"

    #
    # j not changed
    #
    assert j_copy == j
