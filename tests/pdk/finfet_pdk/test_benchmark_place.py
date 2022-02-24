import time
import pytest
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits


cleanup = True


@pytest.mark.parametrize('params', [None, "--select_in_ILP"])
def test_bench_1(params):
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "AutoConstraint", "isTrue": False, "propagate": True},
        {"constraint": "GroupBlocks", "instances": ["mn1", "mn2"], "name": "g1"},
        {"constraint": "GroupBlocks", "instances": ["mn3", "mn4"], "name": "g2"},
        {"constraint": "GroupBlocks", "instances": ["mp5", "mp6"], "name": "g3"},
        {"constraint": "Order", "direction": "top_to_bottom", "instances": ["g3", "g2", "g1"]},
        {"constraint": "AspectRatio", "subcircuit": name, "ratio_low": 0.5, "ratio_high": 2}
    ]
    example = build_example(name, netlist, constraints)
    s = time.time()
    ckt_dir, run_dir = run_example(example, log_level='DEBUG', additional_args=params)
    e = time.time()
    print('Elapsed time:', e-s)
    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
