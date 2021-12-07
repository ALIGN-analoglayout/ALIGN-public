import pathlib
import json

from align.compiler.compiler import compiler_input, call_primitive_generator, constraint_generator, compiler_output


def test_cap():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / "test_cap.sp"
    gen_const_path = mydir.parent / "Results" / "TEST_CAP.verilog.json"
    gold_const_path = (
        mydir.parent.parent / "files" / "test_results" / "test_cap.const.json"
    )

    updated_ckt = compiler_input(test_path, "test_cap", pdk_path, config_path)
    assert updated_ckt.find("TEST_CAP")
    primitives, generators = call_primitive_generator(updated_ckt, pdk_path, True)
    verilog_tbl = constraint_generator(updated_ckt, generators)
    compiler_output(
        updated_ckt,
        "TEST_CAP",
        verilog_tbl,
        pathlib.Path(__file__).parent / "Results",
    )
    assert "CAP_30f" in primitives.keys()
    with open(gen_const_path, "r") as const_fp:
        gen_const = next(
            x for x in json.load(const_fp)["modules"] if x["name"] == "TEST_CAP"
        )["constraints"]
        gen_const.sort(key=lambda item: item.get("constraint"))
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const


# TODO: cap array testing
