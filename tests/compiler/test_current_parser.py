import pathlib

from align.compiler.read_netlist import SpiceParser
from align.compiler.match_graph import Annotate
from align.compiler.create_database import CreateDatabase
from align.compiler.user_const import ConstraintParser

def test_parser1():
    test_path=(pathlib.Path(__file__).parent.parent / 'files' / 'test_circuits' / 'test1.sp').resolve()
    sp = SpiceParser(test_path,"test1",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 10
    assert len(g["ports"]) == 4 
    assert 'vss' in g["ports"] # A port name 0 should be changed to vss

def test_parser2():
    test_path=(pathlib.Path(__file__).parent.parent / 'files' / 'test_circuits' / 'test2.sp').resolve()
    sp = SpiceParser(test_path,"test2",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 12


def test_parser3():
    test_path=pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_circuits'/ 'ota'/ 'ota.sp'
    sp = SpiceParser(test_path,"ota",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 25 # number of nodes in OTA
    test_path=pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_circuits'/ 'basic_template.sp'
    lib_sp =  SpiceParser(test_path)
    lib_list = lib_sp.sp_parser()
    assert len(lib_list) == 46 ## 18 subckt in basic template
    return(g["graph"], lib_list)

def test_match_ota():
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    input_dir = pathlib.Path(__file__).resolve().parent.parent / 'files' / 'test_circuits'
    g,lib_list = test_parser3()
    design_setup = {'POWER':['vdd'],'GND':['vss'], 'DIGITAL':[], 'CLOCK':[],'NO_ARRAY':[]}
    all_lef = ['Switch_NMOS','Switch_PMOS','CMC_PMOS','CMC_S_NMOS_B','DP_NMOS_B','SCM_NMOS']
    const_parse = ConstraintParser(pdk_dir, input_dir)
    create_data = CreateDatabase(g,const_parse)
    hier_graph_dict = create_data.read_inputs("ota")
    annotate = Annotate(hier_graph_dict, design_setup,lib_list,all_lef)
    mapped_graph_list = annotate._mapped_graph_list(g, lib_list,['vdd!','vss'])
    assert 'Switch_NMOS' in mapped_graph_list.keys()
    assert 'Switch_PMOS' in mapped_graph_list.keys()
    assert 'CMC_PMOS' in mapped_graph_list.keys()
    assert 'CMC_S_NMOS_B' in mapped_graph_list.keys()
    assert 'DP_NMOS_B' in mapped_graph_list.keys()

    hier_graph_dict['ota']['graph'] = annotate._reduce_graph(g, "ota", mapped_graph_list, hier_graph_dict['ota']['constraints'])
    assert len( hier_graph_dict['ota']['graph'].nodes()) == 19
    return hier_graph_dict

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

