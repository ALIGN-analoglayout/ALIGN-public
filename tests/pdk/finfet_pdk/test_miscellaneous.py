import textwrap
from .utils import get_test_id, build_example, run_example
import align.pdk.finfet
import pathlib
from align.compiler.read_library import read_lib


def test_read_lib():
    pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent
    config_path = pdk_dir.parent.parent / 'config'
    lib = read_lib(pdk_dir,  config_path)
    assert lib.find('INV')
    assert not lib.find('CASCODED_CMC_PMOS')


def test_floating_pin():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} d g s1 s2 vccx vssx floating_pin
    qp0 d g s1 vccx p m=1 nf=2 w=90e-9
    qn0 d g s2 vssx n m=1 nf=2 w=90e-9
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "DoNotRoute", "nets": ["vccx", "vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=False, n=1)
