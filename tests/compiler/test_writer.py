import pathlib

from align.compiler.write_verilog_lef import WriteVerilog, WriteSpice, generate_lef,WriteCap
from align.compiler.write_constraint import WriteConst, FindArray
from test_current_parser import test_match

def test_verilog_writer():
    subckts = test_match()
    unit_cap = 12
    unit_mos = 12
    VERILOG_FP = open(pathlib.Path(__file__).parent / 'ota.v', 'w')
    SP_FP = open(pathlib.Path(__file__).parent / 'ota_blocks.sp', 'w')
    available_cell_generator = ['Switch_PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS', 'CMC_PMOS_S', 'DCL_NMOS']
    for subckt in subckts:
        for _, attr in subckt['graph'].nodes(data=True):
            if 'values' in attr:
                block_name, _ = generate_lef(attr['inst_type'], attr["values"],
                            available_cell_generator, unit_mos, unit_cap)
                block_name_ext = block_name.replace(attr['inst_type'],'')
        wv = WriteVerilog(subckt["graph"],subckt["name"]  , subckt["ports"], subckts,['vdd!','vss'])
        wv.print_module(VERILOG_FP)
        if subckt["name"] in available_cell_generator:
            ws = WriteSpice(subckt["graph"],subckt["name"]+block_name_ext  , subckt["ports"], subckts)
            ws.print_subckt(SP_FP)
        WriteConst(subckt["graph"], pathlib.Path(__file__).parent, subckt["name"], subckt['ports'],[])
        all_array=FindArray(subckt["graph"], pathlib.Path(__file__).parent, subckt["name"] )
        WriteCap(subckt["graph"], pathlib.Path(__file__).parent, subckt["name"],  unit_cap,all_array)   
    VERILOG_FP.close()
    SP_FP.close()

def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
