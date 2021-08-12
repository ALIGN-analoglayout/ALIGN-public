import pathlib
from align import primitive

from align.compiler.write_verilog_lef import WriteVerilog
from align.primitive import generate_primitive_lef
from align.compiler.find_constraint import FindConst
from align.schema.constraint import ConstraintDB
from align.schema.subcircuit import SubCircuit
from test_compiler import test_compiler

def test_verilog_writer():
    ckt_data = test_compiler()
    assert ckt_data.find('OTA')

    available_cell_generator = ['NMOS','PMOS', 'CMC_NMOS', 'CMC_PMOS', 'DP_NMOS_B', 'CMC_S_NMOS_B', 'DCL_NMOS', 'SCM_NMOS']
    design_config={
            "vt_type":["SLVT","HVT","LVT","RVT"],
            "unit_size_nmos":12,
            "unit_size_pmos":12,
            "unit_size_cap":12,
            "unit_height_res":600
            }

    verilog_tbl = { 'modules': [], 'global_signals': []}

    for subckt in ckt_data:
        if not isinstance(subckt, SubCircuit):
            continue
        name = subckt.name
        primitives = {}
        for ele in subckt.elements:
            if ele.model in available_cell_generator:
                assert generate_primitive_lef(ele, str(ckt_data.find(ele.model)),
                            available_cell_generator, primitives, design_config )

        if name in available_cell_generator or name.split('_type')[0] in available_cell_generator:
            const = ConstraintDB()
        else:
            FindConst(ckt_data, name, ['vdd!'])


        wv = WriteVerilog(subckt, ckt_data, ['vdd!','vss'])
        verilog_tbl['modules'].append( wv.gen_dict())

