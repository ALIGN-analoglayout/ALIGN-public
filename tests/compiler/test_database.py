from operator import sub
import pathlib
from align.schema import SubCircuit, constraint
from align.compiler.compiler import compiler_input, generate_hierarchy
from utils import clean_data, build_example, get_test_id
import textwrap
from pytest import raises

align_home = pathlib.Path(__file__).resolve().parent.parent.parent
pdk_path = align_home / "pdks" / "FinFET14nm_Mock_PDK"
config_path = pathlib.Path(__file__).resolve().parent.parent / "files"
out_path = pathlib.Path(__file__).resolve().parent / "Results"

def multi_domain_power_ckt(name):
    netlist = textwrap.dedent(
        f"""\
        .subckt test D G S B S1
        * @: PowerPorts(ports=['D1'])
        * @: GroundPorts(ports=['S1'])
        * @: ClockPorts(ports=['G1'])
        mn1 D G S B n nfin=8 nf=2
        mn2 D1 G2 S1 B n nfin=8 nf=4
        .ends test
        .subckt {name} D G S B
        xi1 D G S B S1 test
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

def test_global_param():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .param tf=12
        .subckt {name} D G S B
        mn1 D G S B n nfin=tf nf=2 m=8
        .ends {name}
    """
    )
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    assert ckt_library.find(name).get_element("MN1")
    assert ckt_library.find(name).get_element("MN1").parameters["NFIN"] == "12"
    clean_data(name)


def test_global_param_1():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .param p2=2
        .subckt {name} D G S B
        .param p1=p2
        M0 D G S B nmos nfin=12 nf=p1 m=8
        .ends {name}
        """
    )
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    assert ckt_library.find(name).get_element('M0').parameters["NF"] == '2'
    clean_data(name)

def test_generator():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt {name} D G S B
        * @: Generator(name='mos')
        mn1 D G S B n nfin=12 nf=2
        mn2 S G D B n nfin=12 nf=2
        .ends {name}
    """
    )
    example = build_example(name, netlist, constraints=[])
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    assert len(ckt_library.find(name).constraints) == 1
    clean_data(name)


def test_propogate_global_const():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = multi_param_ckt(name)
    constraints = [
        {"constraint": "ConfigureCompiler", "remove_dummy_hierarchies": False, "propagate": True}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    assert len(ckt_library.find("PARAM_MOS").constraints) == 1
    clean_data(name)


def test_special_port_propagation():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt test D G S B
        mn1 D G S B n nfin=8 nf=2
        mn2 D1 G2 S1 B n nfin=8 nf=4
        .ends test
        .subckt {name} D G S B
        xi1 D G S B test
        .ends {name}
        """
    )
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ClockPorts", "ports": ["G"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    consts = ckt_library.find("TEST").constraints
    special_ports = {}
    for const in consts:
        if isinstance(const, constraint.PowerPorts):
            special_ports["PWR"] = const.ports
        elif isinstance(const, constraint.GroundPorts):
            special_ports["GND"] = const.ports
        elif isinstance(const, constraint.ClockPorts):
            special_ports["CLK"] = const.ports
    assert special_ports == {"PWR": ["D"], "GND": ["S"], "CLK": ["G"]}
    clean_data(name)


def test_multipower_domain_propagation():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = multi_domain_power_ckt(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ClockPorts", "ports": ["G"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    consts = ckt_library.find("TEST").constraints
    special_ports = {}
    for const in consts:
        if isinstance(const, constraint.PowerPorts):
            special_ports["PWR"] = const.ports
        elif isinstance(const, constraint.GroundPorts):
            special_ports["GND"] = const.ports
        elif isinstance(const, constraint.ClockPorts):
            special_ports["CLK"] = const.ports
    assert special_ports == {"PWR": ["D1", "D"], "GND": ["S1", "S"], "CLK": ["G1", "G"]}


def test_power_and_signal_ckt():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt test D G S B S1
        mn1 D G S B n nfin=8 nf=2
        mn2 D1 G2 S1 B n nfin=8 nf=4
        .ends test
        .subckt {name} D G S B
        xi1 D G S B S1 test
        xi2 D G signal B S1 test
        .ends {name}
        """
    )
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ClockPorts", "ports": ["G"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    consts = ckt_library.find("TEST").constraints
    special_ports = {}
    for const in consts:
        if isinstance(const, constraint.PowerPorts):
            special_ports["PWR"] = const.ports
        elif isinstance(const, constraint.GroundPorts):
            special_ports["GND"] = const.ports
        elif isinstance(const, constraint.ClockPorts):
            special_ports["CLK"] = const.ports
    assert special_ports == {"PWR": ["D"], "GND": ["S"], "CLK": ["G"]}

def test_multi_param():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = multi_param_ckt(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ConfigureCompiler", "remove_dummy_hierarchies": False}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
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
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    ckt = ckt_library.find(name)
    assert ckt
    assert ckt.get_element("XI1"), f"all instances{[ele.name for ele in ckt.elements]}"
    assert ckt.get_element("XI1").parameters["NFIN"] == "16"
    assert ckt.get_element("XI2")
    assert ckt.get_element("XI2").parameters["NFIN"] == "24"
    assert ckt.get_element("XI3")
    assert ckt.get_element("XI3").parameters["NFIN"] == "24"
    assert ckt.get_element("XI4")
    assert ckt.get_element("XI4").parameters["NFIN"] == "64"
    clean_data(name)


def test_multi_param_skip():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt param_mos D G S B
        .param tf=12 n=2
        mn0 D G S B n nfin=tf nf=n m=8
        .ends param_mos
        .subckt param_mos_1 D G S B
        .param tf=12 n=2
        mn1 D G S B nmos_rvt nfin=tf nf=n m=8
        .ends param_mos_1
        .subckt {name} D G S B
        xi1 D G S B param_mos tf=16 n=2
        xi2 D G S B param_mos_1 tf=32 n=2
        xi3 D G S B param_mos tf=32 n=2
        .ends {name}
        """
    )
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ConfigureCompiler", "remove_dummy_hierarchies": False}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    all_modules = set([name, "PARAM_MOS", "PARAM_MOS_1", "PARAM_MOS_2"])
    available_modules = set(
        [module.name for module in ckt_library if isinstance(module, SubCircuit)]
    )
    assert available_modules == all_modules, f"{available_modules}"
    assert ckt_library.find("PARAM_MOS").parameters["TF"] == "16"
    assert ckt_library.find("PARAM_MOS_1").parameters["TF"] == "32"
    assert ckt_library.find("PARAM_MOS_2").parameters["TF"] == "32"
    assert ckt_library.find("PARAM_MOS").get_element("MN0").parameters["NFIN"] == "16"
    assert ckt_library.find("PARAM_MOS_1").get_element("MN1").parameters["NFIN"] == "32"
    assert ckt_library.find("PARAM_MOS_2").get_element("MN0").parameters["NFIN"] == "32"
    clean_data(name)


def test_preprocessing_SD():
    name = f'ckt_{get_test_id()}'.upper()
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
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ConfigureCompiler", "remove_dummy_hierarchies": False}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
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


def test_subckt_generator():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    mp0 o a vccx vccx p w=45e-9 m=1 nf=1
    mn0 o a vssx vssx n w=45e-9 m=1 nf=1
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v0 vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = []
    import align.pdk.finfet
    pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_dir, config_path)
    assert ckt_library.find('DIG22INV').generator['name'] == 'DIG22INV'


def test_model_generator():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} vi vo
    xi0 vi vo tfr
    .ends {name}
    """)
    constraints = []
    import align.pdk.finfet
    pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent
    result_path = pathlib.Path(__file__).parent / ('run_'+name)
    example = build_example(name, netlist, constraints)
    primitives = generate_hierarchy(example, name, result_path,False, pdk_dir)
    all_modules = [subckt.name for subckt in primitives if subckt.name.startswith('TFR_2T')]
    assert all_modules
    assert primitives.find(all_modules[0]).generator['name'] == 'TFR'
    clean_data('run_'+name)
    clean_data(name)

def test_generic_generator():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} vi vo
    xi0 vi vo tfr_prim
    .ends {name}
    """)
    constraints = []
    import align.pdk.finfet
    pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent
    result_path = pathlib.Path(__file__).parent / ('run_'+name)
    example = build_example(name, netlist, constraints)
    primitives = generate_hierarchy(example, name, result_path, False, pdk_dir)
    all_modules = [subckt.name for subckt in primitives if subckt.name.startswith('TFR_PRIM_')]
    assert all_modules
    assert primitives.find(all_modules[0]).generator['name'] == 'TFR_PRIM'
    clean_data('run_'+name)
    clean_data(name)


def test_unimplemented_generator():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} vi vo
    xi0 vi vo unimplemented
    .ends {name}
    """)
    constraints = []
    result_path = pathlib.Path(__file__).parent / ('run_'+name)
    example = build_example(name, netlist, constraints)
    with raises(AssertionError):
        generate_hierarchy(example, name, result_path, False, pdk_path)


def test_global_param_2():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .param p2=24 p3=4
        .subckt param_mos D G S B
        .param tf=12 n=2
        m0 D G S B n nfin=tf nf=n m=8
        .ends param_mos

        .subckt {name} D G S B
        .param p1=p2 pn=2
        xi1 D G S B param_mos tf=16 n=pn
        xi2 D G S B param_mos tf=p1 n=p3
        .ends {name}
        """
    )
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    assert ckt_library.find(name).get_element('XI1').parameters["NFIN"] == '16'
    assert ckt_library.find(name).get_element('XI1').parameters["NF"] == '2'
    assert ckt_library.find(name).get_element('XI2').parameters["NFIN"] == '24'
    assert ckt_library.find(name).get_element('XI2').parameters["NF"] == '4'
    clean_data(name)


def test_base_model():
    name = f'ckt_{get_test_id()}'.upper()
    netlist = textwrap.dedent(
        f"""\
        .subckt param_mos D G S B
        m0 D G S B nmos nfin=12 nf=n m=8
        m1 S G D B nmos nfin=12 nf=n m=8
        .ends param_mos

        .subckt {name} D G S B
        xi1 D G S B param_mos
        .ends {name}
        """
    )
    constraints = [
        {"constraint": "PowerPorts", "ports": ["D"]},
        {"constraint": "GroundPorts", "ports": ["S"]},
        {"constraint": "ConfigureCompiler", "merge_parallel_devices": False}
    ]
    example = build_example(name, netlist, constraints)
    ckt_library, _ = compiler_input(example, name, pdk_path, config_path)
    assert ckt_library.find('PARAM_MOS').get_element('M0').pins == {"D": "D", "G": "G", "S": "S", "B": "B"}
    assert ckt_library.find('PARAM_MOS').get_element('M1').pins == {"D": "D", "G": "G", "S": "S", "B": "B"}
    clean_data(name)

