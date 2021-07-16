import pathlib

from align.compiler.write_verilog_lef import write_verilog, WriteVerilog, generate_lef
from align.compiler.find_constraint import FindConst
from align.schema.constraint import ConstraintDB
from align.compiler.common_centroid_cap_constraint import CapConst
from test_compiler import test_compiler

def test_verilog_writer():
    ckt_data = test_compiler()
    assert ckt_data.find('OTA')
    result_dir = pathlib.Path(__file__).parent /'Results'

    available_cell_generator = ['PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS_B', 'CMC_S_NMOS_B', 'DCL_NMOS', 'SCM_NMOS']
    design_config={
            "vt_type":["SLVT","HVT","LVT","RVT"],
            "unit_size_nmos":12,
            "unit_size_pmos":12,
            "unit_size_cap":12,
            "unit_height_res":600
            }

    verilog_tbl = { 'modules': [], 'global_signals': []}

    for name, subckt in ckt_data.items():
        for _, attr in subckt['graph'].nodes(data=True):
            if 'values' in attr:
                block_name, _ = generate_lef(attr['inst_type'], attr,
                            available_cell_generator, design_config )
                block_name_ext = block_name.replace(attr['inst_type'],'')

        if name in available_cell_generator or name.split('_type')[0] in available_cell_generator:
            const = ConstraintDB()
        else:
            const = FindConst(subckt["graph"], name, subckt['ports'], subckt['ports_weight'], ConstraintDB(), ['vdd!'])
            const = CapConst(subckt["graph"], name, design_config["unit_size_cap"], const, True)
            ckt_data[name] = subckt.copy(
                update={'constraints': const}
            )

        wv = WriteVerilog(name, subckt["ports"], subckts, ['vdd!','vss'])
        verilog_tbl['modules'].append( wv.gen_dict())

    with (result_dir / 'ota.v').open( 'wt') as fp:
        write_verilog( verilog_tbl, fp)


def find_ports(graph):
    ports = []
    for node, attr in graph.nodes(data=True):
        if 'net_type' in attr:
            if attr['net_type'] == "external":
                ports.append(node)
    return ports
