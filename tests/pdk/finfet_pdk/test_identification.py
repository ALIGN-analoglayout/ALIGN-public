import json
import textwrap
from .utils import get_test_id, build_example, run_example


def test_identification():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} cm vb ip1 ip2 in1 in2 on1 on2 op1 op2 vssx
    mn01 cm   vb vssx vssx n w=360e-9 m=1 nf=2
    mn02 cm   vb vssx vssx n w=360e-9 m=1 nf=2 dd=1
    *** case 1: DP1 (dd=0 by default)
    mn1 on1 ip1   cm vssx n w=360e-9 m=1 nf=2
    mn2 op1 in1   cm vssx n w=360e-9 m=1 nf=2 dd=0
    *** case 2: Not a diffpair
    mn3 on1 ip2   cm vssx n w=360e-9 m=1 nf=2
    mn4 op1 in2   cm vssx n w=360e-9 m=1 nf=2 dd=1
    *** case 3: DP2
    mn5 on2 ip2   cm vssx n w=360e-9 m=1 nf=2 dd=2
    mn6 op2 in2   cm vssx n w=360e-9 m=1 nf=2 dd=2
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

        def find_instance(instances, pattern):
            inst = [key for key in instances.keys() if all([p in key for p in pattern])]
            assert len(inst) > 0, f'{pattern} not found in {instances.keys()}'
            assert len(inst) == 1, f'Collision: {inst}'
            return instances[inst[0]]

        atn = 'abstract_template_name'

        mn01 = find_instance(instances, ['MN01'])
        mn02 = find_instance(instances, ['MN02'])
        assert mn01[atn] != mn02[atn], 'Collision'

        dp12 = find_instance(instances, ['MN1', 'MN2'])
        dp56 = find_instance(instances, ['MN5', 'MN6'])
        assert dp12[atn] != dp56[atn], 'Collision'

        inst = [key for key in instances.keys() if all([p in key for p in ['MN3', 'MN4']])]
        assert len(inst) == 2, 'MN3 and MN4 should be distinct primitives'
