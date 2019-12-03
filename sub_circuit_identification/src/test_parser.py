import os
import shutil
from read_netlist import SpiceParser
from read_library import LibSpiceParser
from match_graph import reduce_graph, _mapped_graph_list
from write_verilog_lef import WriteVerilog, WriteSpice, generate_lef

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
    assert len(g.nodes()) == 25 # number of nodes in OTA
    lib_sp = LibSpiceParser("../basic_library/basic_template.sp")
    lib_list = lib_sp.sp_parser()
    shutil.rmtree("library_graphs")
    assert len(lib_list) == 24 ## 24 subckt in basic template
    return(g, lib_list)

def test_match():
    g,lib_list =test_parser3()
    mapped_graph_list = _mapped_graph_list(g, lib_list)
    assert 'CMC_NMOS' in mapped_graph_list.values()
    assert 'CMC_PMOS_S' in mapped_graph_list.values()
    assert 'CMC_NMOS' in mapped_graph_list.values()
    assert 'DP_NMOS' in mapped_graph_list.values()
    subckts_created, reduced_graph = reduce_graph(g, mapped_graph_list, lib_list)
    assert len(reduced_graph.nodes()) == 16
    subckts_created.append({
            "name": "ota",
            "lib_graph":reduced_graph ,
            "ports":find_ports(reduced_graph),
            "size": len(reduced_graph.nodes())
        })
    print(reduced_graph.nodes())
    print(subckts_created)
    return subckts_created

def test_verilog_writer():
    subckts = test_match()
    unit_cap = 12
    unit_mos = 12
    VERILOG_FP = open('ota.v', 'w')
    LEF_FP = open('ota_lef.sh', 'w')
    SP_FP = open('ota_blocks.sp', 'w')
    available_cell_generator = ['Switch_PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS', 'CMC_PMOS_S', 'DCL_NMOS']
    for subckt in subckts:
        for _, attr in subckt['lib_graph'].nodes(data=True):
            if 'values' in attr:
                block_name = generate_lef(LEF_FP, attr['inst_type'], attr["values"],
                            available_cell_generator, unit_mos, unit_cap)
                block_name_ext = block_name.replace(attr['inst_type'],'')
        wv = WriteVerilog(subckt["lib_graph"],subckt["name"]  , subckt["ports"], subckts)
        wv.print_module(VERILOG_FP)
        if subckt["name"] in available_cell_generator:
            ws = WriteSpice(subckt["lib_graph"],subckt["name"]+block_name_ext  , subckt["ports"], subckts)
            ws.print_subckt(SP_FP)
    VERILOG_FP.close()
    LEF_FP.close()
    SP_FP.close()
    os.remove('ota.v')
    os.remove('ota_lef.sh')
    os.remove('ota_blocks.sp')

def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
if __name__ == '__main__':
    test_parser3()
