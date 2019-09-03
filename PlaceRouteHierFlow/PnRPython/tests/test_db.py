import json
from pnrdb import hierNode, PnRDBEncoder

def test_A():
    with open("tests/telescopic_ota-freeze.json","rt") as fp:
        j = json.load(fp)
        hN = hierNode(j)

    with open("__json","wt") as fp:
        json.dump( hN, fp=fp, cls=PnRDBEncoder, indent=2)

    with open("__json2","wt") as fp:
        json.dump( j, fp=fp, indent=2)

    with open("__json","rt") as fp:
        jj = json.load(fp)

    assert j == jj
