import json
import pytest
import textwrap
from .utils import get_test_id, build_example, run_example


def dump_simplified_json(modules, filename):
    # simplify for debug
    modules_simple = dict()
    for k, v in modules.items():
        modules_simple[k] = dict()
        modules_simple[k]['instances'] = list()
        for inst in v['instances']:
            new_inst = {k: v for k, v in inst.items()}
            del new_inst['fa_map']
            # del new_inst['abstract_template_name']
            modules_simple[k]['instances'].append(new_inst)
    with (filename).open('w') as fp:
        json.dump(modules_simple, fp=fp, indent=2)
    return modules_simple


def find_instance(instances, pattern):
    inst = [key for key in instances.keys() if all([p in key for p in pattern])]
    assert len(inst) > 0, f'{pattern} not found in {instances.keys()}'
    assert len(inst) == 1, f'Collision: {inst}'
    return instances[inst[0]]


def test_collisions():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} cm vb ip1 ip2 in1 in2 on1 on2 op1 op2 vssx
    mn01 cm   vb vssx vssx npv w=360e-9 m=1 nf=2
    mn02 cm   vb vssx vssx npv w=360e-9 m=1 nf=2 dv=1
    *** case 1: DP1 (dd=0 by default)
    mn1 on1 ip1   cm vssx npv w=360e-9 m=1 nf=2
    mn2 op1 in1   cm vssx npv w=360e-9 m=1 nf=2 dv=0
    *** case 2: Not a diffpair
    mn3 on1 ip2   cm vssx npv w=360e-9 m=1 nf=2
    mn4 op1 in2   cm vssx npv w=360e-9 m=1 nf=2 dv=1
    *** case 3: DP2
    mn5 on2 ip2   cm vssx npv w=360e-9 m=1 nf=2 dv=2
    mn6 op2 in2   cm vssx npv w=360e-9 m=1 nf=2 dv=2
    .ends {name}
    .END
    """)
    constraints = [{"constraint": "AutoConstraint", "isTrue": False, "propagate": True}]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, n=1, additional_args=['--flow_stop', '2_primitives'])

    name = name.upper()
    filename = run_dir / '1_topology' / f'{name}.verilog.json'
    assert filename.exists() and filename.is_file(), f'File not found:{filename}'
    with (filename).open('rt') as fp:
        data = json.load(fp)
        modules = {m['name']: m for m in data['modules']}
        instances = {inst['instance_name']: inst for inst in modules[name]['instances']}

        filename = run_dir / '1_topology' / f'{name}_simple.verilog.json'
        _ = dump_simplified_json(modules, filename)

        atn = 'abstract_template_name'

        dp12 = find_instance(instances, ['MN1', 'MN2'])
        dp56 = find_instance(instances, ['MN5', 'MN6'])
        assert dp12[atn] != dp56[atn], 'Collision of diff pairs'

        inst = [key for key in instances.keys() if any([p in key for p in ['MN3', 'MN4']])]
        assert len(inst) == 2, 'MN3 and MN4 should be distinct primitives'

        mn01 = find_instance(instances, ['MN01'])
        mn02 = find_instance(instances, ['MN02'])
        assert mn01[atn] != mn02[atn], 'Collision of mn01 and mn02'


def test_disable_fix_merge():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} d1 g1 s1 d2 g2 s2 vssx
    mn01 d1 g1 s1 vssx n w=360e-9 m=1 nf=2
    mn02 d1 g1 s1 vssx n w=360e-9 m=1 nf=2
    mn03 d2 g2 i2 vssx n w=360e-9 m=1 nf=2
    mn04 i2 g2 s2 vssx n w=360e-9 m=1 nf=2
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True},
        {"constraint": "FixSourceDrain", "isTrue": False, "propagate": True},
        {"constraint": "MergeSeriesDevices", "isTrue": False, "propagate": True},
        {"constraint": "MergeParallelDevices", "isTrue": False, "propagate": True}
    ]
    example = build_example(name, netlist, constraints)
    _, run_dir = run_example(example, cleanup=False, n=1, additional_args=['--flow_stop', '2_primitives'])

    name = name.upper()
    filename = run_dir / '1_topology' / f'{name}.verilog.json'
    assert filename.exists() and filename.is_file(), f'File not found:{filename}'
    with (filename).open('rt') as fp:
        data = json.load(fp)
        modules = {m['name']: m for m in data['modules']}
        instances = {inst['instance_name']: inst for inst in modules[name]['instances']}
        filename = run_dir / '1_topology' / f'{name}_simple.verilog.json'
        _ = dump_simplified_json(modules, filename)
        assert all([k in instances for k in ['MN01', 'MN02', 'MN03', 'MN04']]), 'Incorrect annotation'


def test_illegal():
    """ stacking parallel devices not allowed """
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} d g s vssx
    mn01 d g i vssx n w=360e-9 m=1 nf=2
    mn02 i g s vssx n w=360e-9 m=1 nf=2
    .ends {name}
    .END
    """)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True}
    ]
    example = build_example(name, netlist, constraints)

    with pytest.raises(AssertionError):
        run_example(example, cleanup=False, n=1, additional_args=['--flow_stop', '2_primitives'])
