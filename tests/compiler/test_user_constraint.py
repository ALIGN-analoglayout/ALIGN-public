import pathlib
import pytest
import json
import shutil

from align.compiler.compiler import compiler_input, constraint_generator
from align.schema.checker import CheckerError

pdk_dir = (
    pathlib.Path(__file__).resolve().parent.parent.parent
    / "pdks"
    / "FinFET14nm_Mock_PDK"
)
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


@pytest.mark.parametrize(
    "dir_name",
    [
        "high_speed_comparator_orderblock",
        "high_speed_comparator_symmblock",
        "high_speed_comparator_portlocation",
        "high_speed_comparator_multiconnection",
        "high_speed_comparator_align",
        "high_speed_comparator_symmnet",
        "high_speed_comparator_compactplacement",
    ],
)
def test_group_block_hsc(dir_name):
    circuit_name = "high_speed_comparator"
    test_path = (
        pathlib.Path(__file__).resolve().parent.parent
        / "files"
        / "test_circuits"
        / dir_name
        / (circuit_name + ".sp")
    )
    updated_cktlib = compiler_input(test_path, circuit_name, pdk_dir, config_path)
    assert updated_cktlib.find("DP")
    assert updated_cktlib.find("CCN")
    assert updated_cktlib.find("CCP")
    assert updated_cktlib.find("INV_P")
    assert updated_cktlib.find("INV_N")
    assert updated_cktlib.find("DP_NMOS_B")
    assert updated_cktlib.find("CCP_S_NMOS_B")
    assert updated_cktlib.find("CCP_PMOS")
    assert updated_cktlib.find("INV")
    result_path = out_path / dir_name
    if result_path.exists() and result_path.is_dir():
        shutil.rmtree(result_path)
    result_path.mkdir(parents=True, exist_ok=False)
    verilog_tbl = constraint_generator(updated_cktlib, dict())
    gen_const_path = result_path / "HIGH_SPEED_COMPARATOR.const.json"
    for module in verilog_tbl["modules"]:
        if module["name"] == "HIGH_SPEED_COMPARATOR":
            gen_const = module["constraints"]
            gen_const.sort(key=lambda item: item.get("constraint"))
            with (gen_const_path).open("wt") as fp:
                json.dump(gen_const, fp=fp, indent=2)
    gold_const_path = (
        pathlib.Path(__file__).resolve().parent.parent
        / "files"
        / "test_results"
        / (dir_name + ".const.json")
    )
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const


@pytest.mark.parametrize("dir_name", ["high_speed_comparator_broken"])
def test_constraint_checking(dir_name):
    circuit_name = "high_speed_comparator"
    test_path = (
        pathlib.Path(__file__).resolve().parent.parent
        / "files"
        / "test_circuits"
        / dir_name
        / (circuit_name + ".sp")
    )
    with pytest.raises(CheckerError):
        compiler_input(test_path, circuit_name, pdk_dir, config_path)


def test_scf():
    mydir = pathlib.Path(__file__).resolve()
    test_path = (
        mydir.parent.parent
        / "files"
        / "test_circuits"
        / "switched_capacitor_filter"
        / "switched_capacitor_filter.sp"
    )
    gold_const_path = (
        mydir.parent.parent
        / "files"
        / "test_results"
        / "switched_capacitor_filter.const.json"
    )

    updated_cktlib = compiler_input(
        test_path, "SWITCHED_CAPACITOR_FILTER", pdk_dir, config_path
    )
    assert updated_cktlib.find("SWITCHED_CAPACITOR_FILTER")
    verilog_tbl = constraint_generator(updated_cktlib, dict())

    for module in verilog_tbl["modules"]:
        if module["name"] == "SWITCHED_CAPACITOR_FILTER":
            gen_const = module["constraints"]
            gen_const.sort(key=lambda item: item.get("constraint"))

    gold_const_path = (
        pathlib.Path(__file__).resolve().parent.parent
        / "files"
        / "test_results"
        / "switched_capacitor_filter.const.json"
    )
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const
