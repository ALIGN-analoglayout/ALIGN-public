import pathlib
import json
import textwrap

from align.compiler.compiler import compiler_input, constraint_generator, annotate_library, generate_hierarchy
from align.schema.subcircuit import SubCircuit
from utils import clean_data, build_example, get_test_id
from align.compiler.gen_abstract_name import PrimitiveLibrary


def test_cap():
    mydir = pathlib.Path(__file__).resolve()
    pdk_path = mydir.parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    config_path = mydir.parent.parent / "files"
    test_path = mydir.parent.parent / "files" / "test_circuits" / "test_cap.sp"
    gold_const_path = (
        mydir.parent.parent / "files" / "test_results" / "test_cap.const.json"
    )

    ckt_lib, prim_lib = compiler_input(test_path, "test_cap", pdk_path, config_path)
    annotate_library(ckt_lib, prim_lib)
    assert ckt_lib.find("TEST_CAP")
    primitives = PrimitiveLibrary(ckt_lib, pdk_path).gen_primitive_collateral()
    all_primitive_names = set([i.name for i in primitives if isinstance(i, SubCircuit)])
    assert all_primitive_names == {'CAP_2T_68022297', 'CAP_2T_90203361', 'NMOS_4T_125789'}
    assert primitives.find('CAP_2T_68022297').elements[0].parameters == {'VALUE': '3E-14', 'PARALLEL': '1', 'STACK': '1'}
    assert primitives.find('CAP_2T_90203361').elements[0].parameters == {'VALUE': '6E-14', 'PARALLEL': '1', 'STACK': '1'}
    mos_param = {'W': '2.7E-07', 'L': '2E-08', 'NFIN': '6', 'PARALLEL': '1', 'M': '1', 'NF': '2', 'STACK': '1'}
    assert primitives.find('NMOS_4T_125789').elements[0].parameters == mos_param
    all_uniq_inst = set([e.name for i in primitives if isinstance(i, SubCircuit) for e in i.elements])
    assert all_uniq_inst == {'M1', 'C1'}
    constraint_generator(ckt_lib)
    gen_const = ckt_lib.find("TEST_CAP").constraints.dict()["__root__"]
    #TODO file changes in separate branch
    gen_const = [const for const in gen_const if const['constraint'] != 'GroupBlocks']
    gen_const.sort(key=lambda item: item.get("constraint"))
    with open(gold_const_path, "r") as const_fp:
        gold_const = json.load(const_fp)
        gold_const.sort(key=lambda item: item.get("constraint"))
    assert gold_const == gen_const


# TODO: cap array testing
def test_group_cap_1():
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} in1 in2 out1 out2
        c2 in1 out1 30e-15
        c1 in2 out2 30e-15
        .ends {name}
    """
    )
    constraints = [
        {"constraint": "GroupCaps", "name": "cap_group1",
         "instances": ["C1", "C2"],
         "num_units": [2, 2],
         "unit_cap": "Cap_12f",
         "dummy": True
         }
    ]
    example = build_example(name, netlist, constraints)
    result_path = pathlib.Path(__file__).parent / ('run_'+name)

    primitives = generate_hierarchy(example, name, result_path, False, pdk_dir)
    modules = [subckt.name for subckt in primitives if isinstance(subckt, SubCircuit)]
    assert modules == ['CAP_12F'], f"missing unit cap primitive"
    clean_data('run_'+name)
    clean_data(name)
