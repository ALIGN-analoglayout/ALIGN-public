import pytest
import textwrap
import json
import shutil
try:
    from .utils import pdk_dir, get_test_id, build_example, run_example, export_to_viewer
except ImportError:
    from utils import pdk_dir, get_test_id, build_example, run_example, export_to_viewer
from align.primitive import main

cleanup = False


def test_dig22inv():
    name = "dig22inv"
    primitive_generator = main.get_generator(name, pdk_dir)
    data = primitive_generator().generate(ports=['A', 'O', 'VCCX', 'VSSX'])
    export_to_viewer("dig22inv", data)


def test_dig_1():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt dig22inv a o vccx vssx
    mp0 o a vccx vccx p w=45e-9 m=1 nf=1
    mn0 o a vssx vssx n w=45e-9 m=1 nf=1
    .ends
    .subckt {name} vi vo vccx vssx
    xi0 vi v1 vccx vssx dig22inv
    xi1 v1 v2 vccx vssx dig22inv
    xi2 v2 vo vccx vssx dig22inv
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False},
        {"constraint": "AlignInOrder", "line": "bottom", "instances": ["xi0", "xi1", "xi2"]}]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=cleanup)
