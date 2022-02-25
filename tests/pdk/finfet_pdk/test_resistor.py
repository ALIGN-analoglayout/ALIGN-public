from align.pdk.finfet import tfr_prim
from .utils import export_to_viewer
import json
import textwrap
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits


def test_zero():
    pg = tfr_prim()
    data = pg.generate(ports=['a', 'b'])
    export_to_viewer("test_tfr_0", data)


def test_res_hier():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = [{"constraint": "AutoConstraint", "isTrue": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=True, n=1, additional_args=['--flow_stop', '2_primitives'])


def test_res_flat():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} v1 v2 v3 vssx
    xr1 v1 vssx tfr_flat w=1 l=1
    xr2 v2 vssx tfr_flat w=1 l=2
    xr3 v3   vm tfr_flat w=1 l=3
    xr4 vm vssx tfr_flat w=1 l=3
    .ends {name}
    .END
    """)
    constraints = [{"constraint": "AutoConstraint", "isTrue": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, n=1, log_level='DEBUG', additional_args=['--flow_stop', '3_pnr:prep'])

    name = name.upper()
    with (run_dir / '1_topology' / '__primitives_library__.json').open('rt') as f1:
        primitives = json.load(f1)
        with (run_dir / '1_topology' / f'{name}.verilog.json').open('rt') as f2:
            hierarchy = json.load(f2)

            atn = set()
            for primitive in primitives:
                if 'generator' in primitive:
                    atn.add(primitive['name'])

            modules = {e['name']: e for e in hierarchy['modules']}
            instances = {i['instance_name']: i for i in modules[name]['instances']}

            assert instances['X_XR3']['abstract_template_name'] == instances['X_XR4']['abstract_template_name']

            for k, v in instances.items():
                assert v['abstract_template_name'] in atn, f"Abstract not found: {v['abstract_template_name']}"
    shutil.rmtree(run_dir)
    shutil.rmtree(example)
