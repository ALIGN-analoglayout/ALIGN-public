import networkx as nx

from src import SpiceParser


def test_parser1():
    sp = SpiceParser("test1.sp")
    g = sp.sp_parser()
    assert len(g.nodes()) == 10

def test_parser2():
    sp = SpiceParser("test2.sp")
    g = sp.sp_parser()
    assert len(g.nodes()) == 12


def test_parser3():
    sp = SpiceParser("ota.sp")
    g = sp.sp_parser()
    assert len(g.nodes()) == 25
