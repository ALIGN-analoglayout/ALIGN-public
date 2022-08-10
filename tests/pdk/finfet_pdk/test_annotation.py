import json
import shutil
import textwrap
from .utils import get_test_id, build_example, run_example
from . import circuits


def test_dcl():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} vbias2 vccx
        mp29     v4 vbias2 v2     vccx p w=2.16e-6 m=1 nf=12
        mp33 vbias2 vbias2 vbias1 vccx p w=1.44e-6 m=1 nf=8
        .ends {name}
        """)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '1_topology' / '__primitives_library__.json').open('rt') as fp:
        primitives = json.load(fp)
        for primitive in primitives:
            if 'generator' in primitive:
                assert primitive["name"].startswith('PMOS') or primitive["name"].startswith('DCL'), f"Incorrect subcircuit identification {primitive}"

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_remove_intermediate_hierarchy():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt sub0 i o vccx vssx
    mp0 o i vccx vccx p w=180e-9 m=1 nf=2
    mn0 o i vssx vssx n w=180e-9 m=1 nf=2
    .ends
    .subckt sub1 in out vccx vssx
    xi0 in out vccx vssx sub0
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx sub1
    xi1 v1 v2 vccx vssx sub1
    xi2 v2 vo vccx vssx sub1
    .ends {name}
    .END
    """)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, additional_args=["--flow_stop", "2_primitives"])
    name = name.upper()
    with (run_dir / "1_topology" / f"{name}.verilog.json").open("rt") as fp:
        hierarchy = json.load(fp)
        modules = {m["name"] for m in hierarchy["modules"]}
        assert name in modules
        assert "SUB0" in modules
        assert "SUB1" not in modules

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)


def test_power_train_thermo():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.power_train_thermo(name)
    constraints = [{"constraint": "PowerPorts", "ports": ["vccx"]}]
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, additional_args=["--flow_stop", "2_primitives"])
    name = name.upper()
    with (run_dir / "1_topology" / f"{name}.verilog.json").open("rt") as fp:
        hierarchy = json.load(fp)
        modules = {m["name"] for m in hierarchy["modules"]}

    # shutil.rmtree(run_dir)
    # shutil.rmtree(ckt_dir)


def test_power_train_thermo_2():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.power_train_thermo(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        # {"constraint": "ConfigureCompiler", "remove_dummy_hierarchies": False}
        ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, additional_args=["--flow_stop", "2_primitives"])
    name = name.upper()
    with (run_dir / "1_topology" / f"{name}.verilog.json").open("rt") as fp:
        hierarchy = json.load(fp)
        modules = {m["name"]: m for m in hierarchy["modules"]}
        constraints = {const["constraint"] for const in modules[name]["constraints"]}
        assert "symmetric_blocks" not in constraints
