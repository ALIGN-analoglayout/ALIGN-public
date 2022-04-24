import pytest
from align.pdk.finfet import tfr_prim
from .utils import export_to_viewer
import json
import textwrap
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits


CLEANUP = True


def test_zero():
    pg = tfr_prim()
    data = pg.generate(ports=['a', 'b'])
    export_to_viewer("test_tfr_0", data)


def test_res_hier():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, n=1, additional_args=['--flow_stop', '2_primitives'])


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
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=1, log_level='DEBUG', additional_args=['--flow_stop', '3_pnr:prep'])

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
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason="For a future PR")
def test_res_one():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
        .subckt {name} a b
        xi0 a b tfr w=2e-6 l=1e-6
        xi1 a b tfr w=2e-6 l=1e-6
        xi2 a b tfr w=2e-6 l=2e-6
        xi3 a b tfr_prim w=2e-6 l=1e-6
        xi4 a b tfr_prim w=2e-6 l=1e-6
        xi5 a b tfr_prim w=2e-6 l=2e-6
        .ends {name}
    """)
    constraints = [{"constraint": "ConfigureCompiler", "auto_constraint": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, n=1, additional_args=['--flow_stop', '2_primitives'])

    name = name.upper()
    with (run_dir / '1_topology' / '__primitives_library__.json').open('rt') as f1:
        primitives = json.load(f1)
        primitives = {p['name']: p for p in primitives}
    with (run_dir / '1_topology' / f'{name}.verilog.json').open('rt') as f1:
        modules = json.load(f1)
        modules = {p['name']: p for p in modules['modules']}

    instances = {inst['instance_name']: inst for inst in modules[name]['instances']}

    def find_instance(instances, pattern):
        inst = [key for key in instances.keys() if all([p in key for p in pattern])]
        assert len(inst) > 0, f'{pattern} not found in {instances.keys()}'
        assert len(inst) == 1, f'Collision: {inst}'
        return instances[inst[0]]

    atn = 'abstract_template_name'

    i0 = find_instance(instances, ['XI0'])
    i1 = find_instance(instances, ['XI1'])
    i2 = find_instance(instances, ['XI2'])
    i3 = find_instance(instances, ['XI3'])
    i4 = find_instance(instances, ['XI4'])
    i5 = find_instance(instances, ['XI5'])
    assert i0[atn] == i1[atn] != i2[atn]
    assert i3[atn] == i4[atn] != i5[atn]

    assert primitives['TFR_PRIM']['base'] == 'TFR'

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
