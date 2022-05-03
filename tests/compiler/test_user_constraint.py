import pathlib
import pytest
import json
import shutil
import textwrap
from align.compiler.compiler import compiler_input, annotate_library
from align.compiler.find_constraint import FindConst
from align.schema.checker import SolutionNotFoundError
from align.schema import SubCircuit
from utils import clean_data, build_example, get_test_id


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
    updated_cktlib, prim_lib = compiler_input(test_path, circuit_name, pdk_dir, config_path)
    annotate_library(updated_cktlib, prim_lib)
    plibs = {"DP", "CCN", "CCP", "INV_P", "INV_N", "DP_NMOS_B", "CCP_S_NMOS_B"}
    assert {plib for subckt in updated_cktlib for plib in plibs if plib in subckt.name} == plibs, f"missing primitive"
    result_path = out_path / dir_name
    if result_path.exists() and result_path.is_dir():
        shutil.rmtree(result_path)
    result_path.mkdir(parents=True, exist_ok=False)
    FindConst(updated_cktlib.find("HIGH_SPEED_COMPARATOR"))
    gen_const = updated_cktlib.find("HIGH_SPEED_COMPARATOR").constraints.dict()["__root__"]
    gen_const.sort(key=lambda item: item.get("constraint"))
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
    with pytest.raises(SolutionNotFoundError):
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

    updated_cktlib, prim_lib = compiler_input(
        test_path, "SWITCHED_CAPACITOR_FILTER", pdk_dir, config_path
    )
    annotate_library(updated_cktlib, prim_lib)

    assert updated_cktlib.find("SWITCHED_CAPACITOR_FILTER")
    FindConst(updated_cktlib.find("SWITCHED_CAPACITOR_FILTER"))
    gen_const = updated_cktlib.find("SWITCHED_CAPACITOR_FILTER").constraints.dict()["__root__"]
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


def test_merged_const():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt param_mos D G S B
        mn1 D G S1 B n nfin=tf nf=n m=8
        mn2 D1 G S B n nfin=tf nf=n m=8
        .ends param_mos

        .subckt {name} D G S B
        xi1 D G S B param_mos
        .ends {name}
    """
    )
    constraints = []
    example = build_example(name, netlist, constraints)
    constraints = [
        {'subcircuit': name,
         'constraints': [{"constraint": "GroundPorts", "ports": ["S"]}]
         },
        {'subcircuit': 'PARAM_MOS',
         'constraints': [{"constraint": "DoNotUseLib", "libraries": ["DP_NMOS_B"]}]
         },
    ]
    with open(example.parent / f"const.json", "w") as fp:
        fp.write(json.dumps(constraints, indent=2))
    ckt_library, _ = compiler_input(example, name, pdk_dir, config_path)
    all_modules = set([name, 'PARAM_MOS'])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    assert ckt_library.find(name).constraints.dict()['__root__'] == [{"constraint": "ground_ports", "ports": ["S"]}]
    assert ckt_library.find('PARAM_MOS').constraints.dict()['__root__'] == [{"constraint": "do_not_use_lib", "libraries": ["DP_NMOS_B"], 'propagate': False},
                                                                            {"constraint": "ground_ports", "ports": ["S"]}]
    clean_data(name)


def test_group_cap():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} in1 out1 out2 vss
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
    mod_const = [
        {"constraint": "group_caps", "name": "cap_group1",
         "instances": ["C1", "C2"],
         "num_units": [2, 2],
         "unit_cap": "Cap_12f",
         "dummy": True
         }
    ]
    example = build_example(name, netlist, constraints)
    cktlib, _ = compiler_input(example, name, pdk_dir, config_path)
    assert cktlib.find(name).constraints.dict()['__root__'] == mod_const
    clean_data(name)



def test_symmnet_unmatched_nets():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} a b
        mn1 a g1 vssx vssx n w=360e-9 nf=2 m=8
        mn2 a g2 vssx vssx n w=360e-9 nf=2 m=8
        mn4 b g3 vssx vssx n w=360e-9 nf=2 m=8
        .ends {name}
    """
    )
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False},
                   {"constraint": "DoNotUseLib", "libraries": ["SCM_PMOS", "CMC_NMOS", "DP_NMOS", "DP_NMOS_B"]},
                   {
                    "constraint": "SymmetricNets",
                    "direction": "V",
                    "net1": "A",
                    "net2": "B",
                    }
                    ]
    example = build_example(name, netlist, constraints)
    cktlib, prim_lib = compiler_input(example, name, pdk_dir, config_path)
    annotate_library(cktlib, prim_lib)
    with pytest.raises(AssertionError):
        FindConst(cktlib.find(name))
    clean_data(name)


def test_symmnet_multi_matched_nets():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} a b
        mn1 a g1 vssx vssx n w=360e-9 nf=2 m=8
        mn2 a g2 vssx vssx n w=360e-9 nf=2 m=8
        mn3 b g3 vssx vssx n w=360e-9 nf=2 m=8
        mn4 b g4 vssx vssx n w=360e-9 nf=2 m=8
        .ends {name}
    """
    )
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False},
                   {"constraint": "DoNotUseLib", "libraries": ["SCM_PMOS", "CMC_NMOS", "DP_NMOS", "DP_NMOS_B"]},
                   {
        "constraint": "SymmetricNets",
        "direction": "V",
        "net1": "A",
        "net2": "B",
    }
    ]
    example = build_example(name, netlist, constraints)
    cktlib, prim_lib = compiler_input(example, name, pdk_dir, config_path)
    annotate_library(cktlib, prim_lib)
    with pytest.raises(AssertionError):
        FindConst(cktlib.find(name))
    clean_data(name)

def test_symmnet_translation():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} a b
        mn1 a g1 vssx vssx n w=360e-9 nf=2 m=8
        mn2 a g2 vssx vssx n w=360e-9 nf=2 m=9
        mn3 b g3 vssx vssx n w=360e-9 nf=2 m=8
        mn4 b g4 vssx vssx n w=360e-9 nf=2 m=9
        .ends {name}
    """
    )
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False},
                   {"constraint": "DoNotUseLib", "libraries": ["SCM_PMOS", "CMC_NMOS", "DP_NMOS", "DP_NMOS_B"]},
                   {
        "constraint": "SymmetricNets",
        "direction": "V",
        "net1": "A",
        "net2": "B",
    }
    ]
    example = build_example(name, netlist, constraints)
    cktlib, prim_lib = compiler_input(example, name, pdk_dir, config_path)
    annotate_library(cktlib, prim_lib)
    FindConst(cktlib.find(name))
    symnet_const = cktlib.find(name).constraints.dict()["__root__"][2]
    modified_symmnet = {
        "constraint": "symmetric_nets",
        "direction": "V",
        "net1": "A",
        "pins1": ["X_MN1/D", "X_MN2/D", "A"],
        "net2": "B",
        "pins2": ["X_MN3/D", "X_MN4/D", "B"]
    }
    assert symnet_const == modified_symmnet, f"incorrect ports identified for symmnet"
    clean_data(name)


def test_groublock_generator():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} a b g1 g2 vssx
        mn1 a g1 vssx vssx n w=360e-9 nf=2 m=8
        mn2 b g2 vssx vssx n w=360e-9 nf=2 m=8
        .ends {name}
    """
    )
    constraints = [{"constraint": "GroupBlocks",  "instances": ["mn1", "mn2"],   "name": "dp1", "generator":{"name":"MOS", "parameters":{"pattern":"cc"}}},
    ]
    example = build_example(name, netlist, constraints)
    cktlib, prim_lib = compiler_input(example, name, pdk_dir, config_path)
    annotate_library(cktlib, prim_lib)
    dp1 = cktlib.find('DP1')
    assert dp1.generator["name"] == 'MOS', f"generator defination error {dp1.generator}"
    assert dp1.constraints.dict()['__root__'][0] == {'constraint':'generator' , 'name': 'MOS', 'parameters':{'pattern':'cc'}}, f"generator constraint error {dp1.constraints}"

    clean_data(name)
    clean_data('run_'+name)
