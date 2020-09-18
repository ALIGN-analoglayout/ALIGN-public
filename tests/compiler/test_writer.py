import pathlib

from align.compiler.write_verilog_lef import WriteVerilog, WriteSpice, generate_lef
from align.compiler.write_constraint import WriteConst
#from align.compiler.create_array_hierarchy import FindArray
from align.compiler.common_centroid_cap_constraint import WriteCap
from test_current_parser import test_match_ota

def test_verilog_writer():
    subckts = test_match_ota()
    unit_cap = 12
    unit_mos = 12
    VERILOG_FP = open(pathlib.Path(__file__).parent / 'ota.v', 'w')
    SP_FP = open(pathlib.Path(__file__).parent / 'ota_blocks.sp', 'w')
    available_cell_generator = ['Switch_PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS', 'CMC_PMOS_S', 'DCL_NMOS', 'SCM_NMOS']
    config_path=pathlib.Path(__file__).resolve().parent / 'design_config.json'
    design_config={
            "vt_type":["HVT","LVT","RVT"],
            "unit_size_nmos":12,
            "unit_size_pmos":12,
            "unit_size_cap":12,
            "unit_height_res":600
            }
    for subckt in subckts:
        for _, attr in subckt['graph'].nodes(data=True):
            if 'values' in attr:
                block_name, _ = generate_lef(attr['inst_type'], attr,
                            available_cell_generator, design_config )
                block_name_ext = block_name.replace(attr['inst_type'],'')
        wv = WriteVerilog(subckt["graph"],subckt["name"]  , subckt["ports"], subckts,['vdd!','vss'])
        wv.print_module(VERILOG_FP)
        if subckt["name"] in available_cell_generator or subckt["name"].split('_type')[0] in available_cell_generator:
            ws = WriteSpice(subckt["graph"],subckt["name"]+block_name_ext  , subckt["ports"], subckts,available_cell_generator)
            ws.print_subckt(SP_FP)
        else:
            #all_array=FindArray(subckt["graph"], pathlib.Path(__file__).parent, subckt["name"],subckt['ports_weight'] )
            all_array = {}
            WriteConst(subckt["graph"], pathlib.Path(__file__).parent, subckt["name"], subckt['ports'],subckt['ports_weight'],all_array,['vdd!'])
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
