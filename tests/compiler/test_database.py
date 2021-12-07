import pathlib
from align.schema import SubCircuit
from align.compiler.compiler import compiler_input
from utils import clean_data, build_example, get_test_id
import textwrap

align_home = pathlib.Path(__file__).resolve().parent.parent.parent
pdk_path = align_home / "pdks" / "FinFET14nm_Mock_PDK"
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"


def mos_ckt(name):
    netlist = textwrap.dedent(
        f"""\
        .param tf=12
        .subckt {name} D G S B
        mn1 D G S B n nfin=tf nf=2 m=8
        .ends {name}
    """
    )
    return netlist


def multi_param_ckt(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt param_mos D G S B
        .param tf=12 n=2
        mn1 D G S B n nfin=tf nf=n m=8
        .ends param_mos

        .subckt {name} D G S B
        xi1 D G S B param_mos tf=16 n=2
        xi2 D G S B param_mos tf=24 n=2
        xi3 D1 G1 S1 B param_mos tf=24 n=2
        xi4 D1 G1 S1 B param_mos tf=64 n=2
        .ends {name}
        """
    )
    return netlist


def multi_param_ckt_with_existing_name(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt param_mos D G S B
        .param tf=12 n=2
        mn1 D G S B n nfin=tf nf=n m=8
        .ends param_mos
        .subckt param_mos_1 D G S B
        .param tf=12 n=2
        mn1 D G S B n nfin=tf nf=n m=8
        mn2 D1 G2 S1 B n nfin=tf nf=n m=16
        .ends param_mos_1

        .subckt {name} D G S B
        xi1 D G S B param_mos tf=16 n=2
        xi2 D G S B param_mos tf=24 n=2
        xi3 D G S B param_mos_1 tf=32 n=2
        .ends {name}
        """
    )
    return netlist


def nested_swap_SD(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt p_mos D G S B
        mn1 S G D B n nfin=12 nf=2 m=8
        .ends p_mos
        .subckt param_mos D G S B
        xi1 D G S B p_mos
        .ends param_mos_1
        .subckt {name} D G S B
        xi1 D G S B param_mos
        .ends {name}
        """
    )
    return netlist


def test_top_param():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = mos_ckt(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    assert ckt_library.find(name).get_element("MN1")
    assert ckt_library.find(name).get_element("MN1").parameters["NFIN"] == "12"
    clean_data(name)


def test_multi_param():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = multi_param_ckt(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "KeepDummyHierarchies", "isTrue": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name, "PARAM_MOS", "PARAM_MOS_1", "PARAM_MOS_2"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    dbc = ckt_library.find(name)
    assert dbc.get_element("XI1").model == "PARAM_MOS"
    assert dbc.get_element("XI2").model == "PARAM_MOS_1"
    assert dbc.get_element("XI3").model == "PARAM_MOS_1"
    assert dbc.get_element("XI4").model == "PARAM_MOS_2"
    assert ckt_library.find("PARAM_MOS").parameters["TF"] == "16"
    assert ckt_library.find("PARAM_MOS_1").parameters["TF"] == "24"
    assert ckt_library.find("PARAM_MOS_2").parameters["TF"] == "64"
    assert ckt_library.find("PARAM_MOS").get_element("MN1").parameters["NFIN"] == "16"
    assert ckt_library.find("PARAM_MOS_1").get_element("MN1").parameters["NFIN"] == "24"
    assert ckt_library.find("PARAM_MOS_2").get_element("MN1").parameters["NFIN"] == "64"
    clean_data(name)


def test_multi_param_remove_dummy():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = multi_param_ckt(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    ckt = ckt_library.find(name)
    assert ckt
    assert ckt.get_element("MI1"), f"all instances{[ele.name for ele in ckt.elements]}"
    assert ckt.get_element("MI1").parameters["NFIN"] == "16"
    assert ckt.get_element("MI2")
    assert ckt.get_element("MI2").parameters["NFIN"] == "24"
    assert ckt.get_element("MI3")
    assert ckt.get_element("MI3").parameters["NFIN"] == "24"
    assert ckt.get_element("MI4")
    assert ckt.get_element("MI4").parameters["NFIN"] == "64"
    clean_data(name)


def test_multi_param_skip():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = multi_param_ckt_with_existing_name(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "KeepDummyHierarchies", "isTrue": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name, "PARAM_MOS", "PARAM_MOS_1", "PARAM_MOS_2"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    assert ckt_library.find("PARAM_MOS").parameters["TF"] == "16"
    assert ckt_library.find("PARAM_MOS_1").parameters["TF"] == "32"
    assert ckt_library.find("PARAM_MOS_2").parameters["TF"] == "24"
    assert ckt_library.find("PARAM_MOS").get_element("MN1").parameters["NFIN"] == "16"
    assert ckt_library.find("PARAM_MOS_1").get_element("MN2").parameters["NFIN"] == "32"
    assert ckt_library.find("PARAM_MOS_2").get_element("MN1").parameters["NFIN"] == "24"
    clean_data(name)


def test_preprocessing_SD():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = nested_swap_SD(name)
    constraints = constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "KeepDummyHierarchies", "isTrue": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name, "PARAM_MOS", "P_MOS"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    assert ckt_library.find("P_MOS").get_element("MN1").parameters["NFIN"] == "12"
    assert ckt_library.find("P_MOS").get_element("MN1").pins == {
        "D": "D",
        "G": "G",
        "S": "S",
        "B": "B",
    }
    clean_data(name)
