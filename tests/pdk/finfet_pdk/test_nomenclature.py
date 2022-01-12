import json
import textwrap
from .utils import get_test_id, build_example, run_example


def test_uniqueness():
    name = f'ckt_{get_test_id()}'
    netlist = textwrap.dedent(f"""\
    .subckt {name} d g s vssx
    mn0 d g s vssx npv w=360e-9 m=1 nf=2
    mn1 d g s vssx npv w=360e-9 m=1 nf=2 source=sig drain=sig
    mn2 d g s vssx npv w=360e-9 m=1 nf=2 source=sig drain=gnd
    mn3 d g s vssx npv w=360e-9 m=1 nf=2 source=gnd drain=sig
    mn4 d g s vssx npv w=360e-9 m=1 nf=2 source=gnd drain=pwr
    .eds {name}
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
        assert len(modules[name]['instances']) == 5
        atn = {inst['abstract_template_name'] for inst in modules[name]['instances']}
        assert len(atn) == 4, f'{atn}'
