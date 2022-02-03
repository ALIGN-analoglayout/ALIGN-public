import pathlib

from align.compiler.compiler import compiler_input, constraint_generator, compiler_output


def test_compiler():
    test_home = pathlib.Path(__file__).resolve().parent.parent
    test_path = test_home / "files" / "test_circuits" / "ota" / "ota.sp"
    pdk_dir = test_home.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = pathlib.Path(__file__).resolve().parent.parent / "files"

    updated_ckt = compiler_input(test_path, "ota", pdk_dir, config_path)
    assert updated_ckt.find("CMC_PMOS")
    assert updated_ckt.find("SCM_NMOS")
    assert updated_ckt.find("CMC_S_NMOS_B")
    assert updated_ckt.find("DP_NMOS_B")
    assert updated_ckt.find("OTA")

    return updated_ckt


def test_compiler_output():
    updated_ckt = test_compiler()
    # Every example should contain a setup file
    verilog_tbl = constraint_generator(
        updated_ckt)
    compiler_output(
        updated_ckt,
        "ota",
        verilog_tbl,
        pathlib.Path(__file__).parent / "Results",
    )
