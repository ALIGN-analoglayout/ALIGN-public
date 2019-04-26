import networkx as nx

from read_netlist import spiceParser


def test_parser1():
    sp = spiceParser("test1.sp")
    g = sp.sp_parser()
    assert len(g.nodes()) == 8


def test_parser2():
    sp = spiceParser("test2.sp")
    g = sp.sp_parser()
    assert len(g.nodes()) == 10
