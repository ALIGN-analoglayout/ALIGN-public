import pathlib

from align.compiler.read_netlist import SpiceParser
from align.compiler.match_graph import reduce_graph, _mapped_graph_list

def test_parser1():
    test_path=(pathlib.Path(__file__).parent / 'test_circuits' / 'test1.sp').resolve()
    sp = SpiceParser(test_path,"test1",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 10
    assert len(g["ports"]) == 4 
    assert 'vss' in g["ports"] # A port name 0 should be changed to vss

def test_parser2():
    test_path=(pathlib.Path(__file__).parent / 'test_circuits' / 'test2.sp').resolve()
    sp = SpiceParser(test_path,"test2",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 12


def test_parser3():
    test_path=pathlib.Path(__file__).resolve().parent / 'test_circuits'/ 'ota'/ 'ota.sp'
    sp = SpiceParser(test_path,"ota",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 25 # number of nodes in OTA
    test_path=pathlib.Path(__file__).resolve().parent / 'test_circuits'/ 'basic_template.sp'
    lib_sp =  SpiceParser(test_path)
    lib_list = lib_sp.sp_parser()
    assert len(lib_list) == 46 ## 18 subckt in basic template
    return(g["graph"], lib_list)

def test_match_ota():
    g,lib_list =test_parser3()
    design_setup = {'POWER':['vdd'],'GND':['vss']}
    all_lef = ['Switch_NMOS','Switch_PMOS','CMC_PMOS','CMC_S_NMOS_B','DP_NMOS_B','SCM_NMOS']
    duplicate = {}
    mapped_graph_list = _mapped_graph_list(g, lib_list,['vdd!','vss'])
    assert 'Switch_NMOS' in mapped_graph_list.keys()
    assert 'Switch_PMOS' in mapped_graph_list.keys()
    assert 'CMC_PMOS' in mapped_graph_list.keys()
    assert 'CMC_S_NMOS_B' in mapped_graph_list.keys()
    assert 'DP_NMOS_B' in mapped_graph_list.keys()
    subckts_created, reduced_graph = reduce_graph(g, mapped_graph_list, lib_list,duplicate,design_setup,all_lef)
    assert len(reduced_graph.nodes()) == 19
    subckts_created.append({
            "name": "ota",
            "graph":reduced_graph ,
            "ports":find_ports(reduced_graph),
            "ports_weight":find_ports_weight(reduced_graph),
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

def find_ports_weight(graph):
    ports=find_ports(graph)
    ports_weight = {}
    for port in ports:
        ports_weight[port] = []
        for nbr in list(graph.neighbors(port)):
            ports_weight[port].append(graph.get_edge_data(nbr,port)['weight'])
    return ports_weight

