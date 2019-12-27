import os
from os.path import dirname, abspath, join, isfile
import sys
# Find code directory relative to our directory
THIS_DIR = dirname(__file__)
CODE_DIR = abspath(join(THIS_DIR, '../../', 'src'))
sys.path.append(CODE_DIR)
from write_verilog_lef import WriteVerilog, WriteSpice, generate_lef,WriteConst,FindArray,WriteCap
from test_parser import test_match

def test_verilog_writer():
    subckts = test_match()
    unit_cap = 12
    unit_mos = 12
    VERILOG_FP = open('ota.v', 'w')
    LEF_FP = open('ota_lef.sh', 'w')
    SP_FP = open('ota_blocks.sp', 'w')
    available_cell_generator = ['Switch_PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS', 'CMC_PMOS_S', 'DCL_NMOS']
    for subckt in subckts:
        for _, attr in subckt['graph'].nodes(data=True):
            if 'values' in attr:
                block_name = generate_lef(LEF_FP, attr['inst_type'], attr["values"],
                            available_cell_generator, unit_mos, unit_cap)
                block_name_ext = block_name.replace(attr['inst_type'],'')
        wv = WriteVerilog(subckt["graph"],subckt["name"]  , subckt["ports"], subckts,['vdd!','vss'])
        wv.print_module(VERILOG_FP)
        if subckt["name"] in available_cell_generator:
            ws = WriteSpice(subckt["graph"],subckt["name"]+block_name_ext  , subckt["ports"], subckts)
            ws.print_subckt(SP_FP)
        WriteConst(subckt["graph"], "./", subckt["name"], subckt['ports'])
        all_array=FindArray(subckt["graph"], "./", subckt["name"] )
        WriteCap(subckt["graph"], "./",subckt["name"],  unit_cap,all_array)   
    VERILOG_FP.close()
    LEF_FP.close()
    SP_FP.close()
    for files in os.listdir('./'):
        if isfile(files):
            if 'ota' in files or 'const' in files: 
                os.remove(files)

def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
#if __name__ == '__main__':
#    test_parser3()
