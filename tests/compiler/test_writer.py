import pathlib

from align.compiler.write_verilog_lef import WriteVerilog, WriteSpice, generate_lef
from align.compiler.write_constraint import WriteConst
from align.compiler.common_centroid_cap_constraint import WriteCap
from test_current_parser import test_match_ota

def test_verilog_writer():
    subckts = test_match_ota()
    assert 'ota' in subckts
    result_dir = pathlib.Path(__file__).parent /'Results'
    VERILOG_FP = open(result_dir / 'ota.v', 'w')
    SP_FP = open(result_dir / 'ota_blocks.sp', 'w')
    available_cell_generator = ['Switch_PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS_B', 'CMC_S_NMOS_B', 'DCL_NMOS', 'SCM_NMOS']
    design_config={
            "vt_type":["SLVT","HVT","LVT","RVT"],
            "unit_size_nmos":12,
            "unit_size_pmos":12,
            "unit_size_cap":12,
            "unit_height_res":600
            }
    for name, subckt in subckts.items():
        for _, attr in subckt['graph'].nodes(data=True):
            if 'values' in attr:
                block_name, _ = generate_lef(attr['inst_type'], attr,
                            available_cell_generator, design_config )
                block_name_ext = block_name.replace(attr['inst_type'],'')
        wv = WriteVerilog(subckt["graph"], name, subckt["ports"], subckts, ['vdd!','vss'])
        wv.print_module(VERILOG_FP)
        if name in available_cell_generator or name.split('_type')[0] in available_cell_generator:
            ws = WriteSpice(subckt["graph"], name+block_name_ext, subckt["ports"], subckts,available_cell_generator)
            ws.print_subckt(SP_FP)
        else:
            const=WriteConst(subckt["graph"], name, subckt['ports'],subckt['ports_weight'],None,['vdd!'])
            WriteCap(subckt["graph"], name,  design_config["unit_size_cap"],const,True)
    VERILOG_FP.close()
    SP_FP.close()

def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
