import pathlib
import textwrap
import shutil

from align.compiler.compiler import compiler_input, annotate_library, compiler_output, PrimitiveLibrary
from align.compiler.match_graph import recursive_replace

test_dir = pathlib.Path(__file__).resolve().parent.parent
pdk_dir = test_dir.parent / "pdks" / "FinFET14nm_Mock_PDK"


def test_compiler():
    test_path = test_dir / "files" / "test_circuits" / "ota" / "ota.sp"
    out_path = pathlib.Path(__file__).parent / "Results"
    config_path = test_dir / "files"
    updated_ckt, prim_lib = compiler_input(test_path, "ota", pdk_dir, config_path)
    annotate_library(updated_ckt, prim_lib)
    plibs = {"CMC_PMOS", "SCM_NMOS", "CMC_S_NMOS_B", "DP_NMOS_B", "OTA"}
    primitives = PrimitiveLibrary(updated_ckt, pdk_dir).gen_primitive_collateral()

    assert {plib for subckt in updated_ckt for plib in plibs if plib in subckt.name} == plibs, f"missing primitive"
    compiler_output(
        updated_ckt,
        "ota",
        out_path,
        primitives
    )
    assert (out_path / 'OTA.verilog.json').exists()


def test_recursive_replace():
    items = ["a", "b", ["c"], [["d"], "e"]]
    update_map = {item: item+item for item in ["A", "B", "C", "D", "E"]}
    recursive_replace(items, update_map)
    assert items == ["AA", "BB", ["CC"], [["DD"], "EE"]]
