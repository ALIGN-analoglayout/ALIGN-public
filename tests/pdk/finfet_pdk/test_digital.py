import pytest
import textwrap
from align.compiler.util import get_generator
from .utils import PDK_DIR, get_test_id, build_example, run_example, export_to_viewer
import shutil
import json

CLEANUP = True

PLACEMENT_ENGINE = [
        ("tamu_sp", ["--router_mode", "no_op", "--placer_sa_iterations", "100"]),
        ("umn_ilp", ["--router_mode", "no_op", "--place_using_ILP"])
]


def test_dig22inv():
    name = "dig22inv"
    primitive_generator = get_generator(name, PDK_DIR)
    data = primitive_generator().generate(ports=['A', 'O', 'VCCX', 'VSSX'])
    export_to_viewer("dig22inv", data)


def test_dig22nor():
    name = "dig22inv"
    primitive_generator = get_generator(name, PDK_DIR)
    data = primitive_generator().generate(ports=['A', 'B', 'O', 'VCCX', 'VSSX'])
    export_to_viewer("dig22nor", data)


def test_dig_primitive():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v2 vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, additional_args=["--flow_stop", "1_topology"])

    name = name.upper()
    filename = run_dir / '1_topology' / '__primitives_library__.json'
    assert filename.exists() and filename.is_file(), f'File not found:{filename}'
    with (filename).open('rt') as fp:
        data = json.load(fp)
        leaves = {m['name']: m for m in data}
        assert "DIG22INV" in leaves

    filename = run_dir / '1_topology' / f'{name}.verilog.json'
    assert filename.exists() and filename.is_file(), f'File not found:{filename}'
    with (filename).open('rt') as fp:
        data = json.load(fp)
        module = data["modules"][0]
        atn = {i["abstract_template_name"] for i in module["instances"]}
        assert atn == {"DIG22INV"}
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_dig_1():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi vo vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False)


def test_dig_3():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v2 vccx vssx dig22inv
    xi2 v2 vo vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["xi0", "xi1", "xi2"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False)


@pytest.mark.parametrize(("engine", "params"), PLACEMENT_ENGINE)
def test_dig_4(engine, params):
    """ Compaction violates PlaceOnGrid constraint """
    name = f'ckt_dig_4_{engine}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v2 vccx vssx dig22inv
    xi2 v2 vo vccx vssx dig22inv
    mn1 vssx vo vssx vssx n w=360e-9 m=2 nf=2
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "Order", "direction": "left_to_right", "instances": ["mn1", "xi0", "xi1", "xi2"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level="DEBUG", additional_args=params)


@pytest.mark.parametrize(("engine", "params"), PLACEMENT_ENGINE)
def test_dig_5(engine, params):
    name = f'ckt_dig_5_{engine}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    .ends
    .subckt dig22nand a b o vccx vssx
    .ends
    .subckt {name} p n nob vccx vssx
    xi0 p en pob vccx vssx dig22nand
    xi1 en p nob vccx vssx dig22nand
    xi2 nob nob vccx vssx dig22inv
    mn1 vssx pob vssx vssx n w=360e-9 m=1 nf=4
    mn2 vssx nob vssx vssx n w=360e-9 m=1 nf=4
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "ConfigureCompiler", "auto_constraint": False, "merge_parallel_devices": False},
        {"constraint": "GroupBlocks", "instance_name": "xdig", "template_name": "dig", "instances": ["xi0", "xi1", "xi2"]},
        {"constraint": "Floorplan", "order": True, "regions": [
            ["xdig"],
            ["mn1", "mn2"]]},
        {"constraint": "Order", "direction": "left_to_right", "instances": ["mn1", "xdig"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, n=1, cleanup=CLEANUP, log_level="DEBUG", additional_args=params)
