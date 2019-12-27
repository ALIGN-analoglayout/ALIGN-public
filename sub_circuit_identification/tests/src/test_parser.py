import os
import shutil
import pathlib
from os.path import dirname, abspath, join
import sys
# Find code directory relative to our directory
THIS_DIR = dirname(__file__)
CODE_DIR = abspath(join(THIS_DIR, '../../', 'src'))
sys.path.append(CODE_DIR)
from read_netlist import SpiceParser
from match_graph import reduce_graph, _mapped_graph_list
from write_verilog_lef import WriteVerilog, WriteSpice, generate_lef

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
    test_path=(pathlib.Path(__file__).parent / 'ota.sp').resolve()
    sp = SpiceParser(test_path,"ota",0)
    g = sp.sp_parser()[0]
    assert len(g["graph"].nodes()) == 25 # number of nodes in OTA
    test_path=(pathlib.Path(__file__).parent / 'basic_template.sp').resolve()
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

#def test_verilog_writer():
#    subckts = test_match()
#    unit_cap = 12
#    unit_mos = 12
#    VERILOG_FP = open('ota.v', 'w')
#    LEF_FP = open('ota_lef.sh', 'w')
#    SP_FP = open('ota_blocks.sp', 'w')
#    available_cell_generator = ['Switch_PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS', 'CMC_PMOS_S', 'DCL_NMOS']
#    for subckt in subckts:
#        for _, attr in subckt['lib_graph'].nodes(data=True):
#            if 'values' in attr:
#                block_name = generate_lef(LEF_FP, attr['inst_type'], attr["values"],
#                            available_cell_generator, unit_mos, unit_cap)
#                block_name_ext = block_name.replace(attr['inst_type'],'')
#        wv = WriteVerilog(subckt["lib_graph"],subckt["name"]  , subckt["ports"], subckts)
#        wv.print_module(VERILOG_FP)
#        if subckt["name"] in available_cell_generator:
#            ws = WriteSpice(subckt["lib_graph"],subckt["name"]+block_name_ext  , subckt["ports"], subckts)
#            ws.print_subckt(SP_FP)
#    VERILOG_FP.close()
#    LEF_FP.close()
#    SP_FP.close()
#    os.remove('ota.v')
#    os.remove('ota_lef.sh')
#    os.remove('ota_blocks.sp')
#
def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
#if __name__ == '__main__':
#    test_parser3()
