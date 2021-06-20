import pytest
try:
    from .helper import *
except:
    from helper import *




@pytest.mark.nightly
def test_case_1():
    constraints = """[
    {"constraint": "GroupBlocks", "instances": ["mmn1", "mmn2"], "name": "dp"},
    {"constraint": "SymmetricBlocks", "direction" : "V", "pairs": [["mmn0"], ["dp"]]},
    {"constraint": "Order", "direction": "top_to_bottom", "instances": ["mmn0", "dp"]}
]
"""
    name = f'comparator_{get_test_id()[5:]}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1)
