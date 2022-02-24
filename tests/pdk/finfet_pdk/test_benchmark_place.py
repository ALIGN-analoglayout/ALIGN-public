import time
import pytest
import shutil
from .utils import build_example, run_example
from . import circuits


cleanup = True


@pytest.mark.parametrize(
    ("name", "params"),
    [
        ("tamu_sp", [""]),
        ("umn_ilp", ["--select_in_ILP"])
    ]
    )
def test_b1(name, params):
    name = f'ckt_b1_{name}'
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
    ckt_dir, run_dir = run_example(example, additional_args=params, cleanup=False)
    e = time.time()
    print('Elapsed time:', e-s)
    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
