import json
import shutil
try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except ImportError:
    from utils import get_test_id, build_example, run_example
    import circuits


def test_dependencies():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.tia(name)
    constraints = []
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False)

    with (run_dir / '2_primitives' / '__primitives__.json').open('rt') as fp:
        primitives = json.load(fp)
        assert 'metadata' in primitives['TFR_PRIM_L_1E06_W_1E06'], 'Metadata not found'

    with (run_dir / '3_pnr' / 'Results' / f'{name.upper()}_0.placement_verilog.json').open('rt') as fp:
        placement = json.load(fp)
        assert 'modules' in placement, 'modules not in placement'

    shutil.rmtree(run_dir)
    shutil.rmtree(ckt_dir)
