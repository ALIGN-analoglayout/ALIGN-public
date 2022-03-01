from align.schema.types import set_context
import pathlib

from align.compiler.write_verilog_lef import WriteVerilog
from align.primitive import generate_primitive_param
from align.compiler.find_constraint import FindConst
from align.schema import constraint
from align.schema.subcircuit import SubCircuit
from test_compiler import test_compiler

mydir = pathlib.Path(__file__).resolve()
pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"

def test_verilog_writer():
    ckt_data = test_compiler()
    assert ckt_data.find("OTA")

    verilog_tbl = {"modules": [], "global_signals": []}

    for subckt in ckt_data:
        if not isinstance(subckt, SubCircuit):
            continue
        gen_const = [True for const in subckt.constraints if isinstance(const, constraint.Generator)]
        if not gen_const:
            wv = WriteVerilog(subckt, ckt_data)
            verilog_tbl["modules"].append(wv.gen_dict())
