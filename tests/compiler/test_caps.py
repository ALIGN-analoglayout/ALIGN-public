import pathlib
import json

from align.compiler.compiler import compiler_input, constraint_generator
from align.compiler.gen_abstract_name import PrimitiveLibrary
from align.schema.subcircuit import SubCircuit


def test_cap():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / "test_cap.sp"
    gold_const_path = (
        mydir.parent.parent / "files" / "test_results" / "test_cap.const.json"
    )

    updated_ckt = compiler_input(test_path, "test_cap", pdk_path, config_path)
    assert updated_ckt.find("TEST_CAP")
    primitives = PrimitiveLibrary(updated_ckt, pdk_path).gen_primitive_collateral()
    all_primitive_names = set([i.name for i in primitives if isinstance(i, SubCircuit)])
    assert all_primitive_names == {'CAP_I1', 'CAP', 'NMOS'}
    assert primitives.find('CAP_I1').elements[0].parameters == {'VALUE': '3E-14', 'PARALLEL': '1', 'STACK': '1'}
    assert primitives.find('CAP').elements[0].parameters == {'VALUE': '6E-14', 'PARALLEL': '1', 'STACK': '1'}
    mos_param = {'W': '2.7E-07', 'L': '2E-08', 'NFIN': '6', 'PARALLEL': '1', 'M': '1', 'NF': '2', 'STACK': '1'}
    assert primitives.find('NMOS').elements[0].parameters == mos_param
    all_uniq_inst = set([e.name for i in primitives if isinstance(i, SubCircuit) for e in i.elements])
    assert all_uniq_inst == {'M0', 'C2', 'C0'}
    constraint_generator(updated_ckt)
    gen_const = updated_ckt.find("TEST_CAP").constraints.dict()["__root__"]
    gen_const.sort(key=lambda item: item.get("constraint"))
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const


# TODO: cap array testing
