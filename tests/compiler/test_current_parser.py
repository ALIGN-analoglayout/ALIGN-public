import pathlib

from align.compiler.read_netlist import SpiceParser
from align.compiler.match_graph import reduce_graph, _mapped_graph_list

def test_parser1():
    test_path=(pathlib.Path(__file__).parent / 'test1.sp').resolve()
    sp = SpiceParser(test_path,"test1",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 10
    assert len(g["ports"]) == 4 
    assert 'vss' in g["ports"] # A port name 0 should be changed to vss

def test_parser2():
    test_path=(pathlib.Path(__file__).parent / 'test2.sp').resolve()
    sp = SpiceParser(test_path,"test2",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 12


def test_parser3():
    test_path=pathlib.Path(__file__).resolve().parent / 'ota.sp'
    sp = SpiceParser(test_path,"ota",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 25 # number of nodes in OTA
    test_path=pathlib.Path(__file__).resolve().parent / 'basic_template.sp'
    lib_sp =  SpiceParser(test_path)
    lib_list = lib_sp.sp_parser()
    #shutil.rmtree("library_graphs")
    assert len(lib_list) == 31 ## 18 subckt in basic template
    return(g["graph"], lib_list)

def test_match():
    g,lib_list =test_parser3()
    mapped_graph_list = _mapped_graph_list(g, lib_list)
    assert 'Switch_NMOS' in mapped_graph_list.keys()
    assert 'Switch_PMOS' in mapped_graph_list.keys()
    assert 'CMC_PMOS_S' in mapped_graph_list.keys()
    assert 'CMC_NMOS' in mapped_graph_list.keys()
    assert 'DP_NMOS' in mapped_graph_list.keys()
    subckts_created, reduced_graph = reduce_graph(g, mapped_graph_list, lib_list)
    assert len(reduced_graph.nodes()) == 16
    subckts_created.append({
            "name": "ota",
            "graph":reduced_graph ,
            "ports":find_ports(reduced_graph),
            "size": len(reduced_graph.nodes())
        })
    print(reduced_graph.nodes())
    print(subckts_created)
    return subckts_created

def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
