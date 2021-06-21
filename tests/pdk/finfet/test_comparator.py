import pytest
try:
    from .helper import *
except:
    from helper import *


@pytest.mark.nightly
def test_no_constraints():
    constraints = """[
]
"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1, cleanup=False)


@pytest.mark.nightly
def test_order1():
    constraints = """[
    {"constraint": "Order", "direction": "left_to_right", "instances": ["mmp7", "mmp8"]}
]
"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1, cleanup=False)


@pytest.mark.nightly
def test_order2():
    constraints = """[
    {"constraint": "Order", "direction": "left_to_right", "instances": ["mmp7", "mmp9"]}
]
"""
    name = f'ckt_{get_test_id()}'
    netlist, netlist_setup = comparator(name)
    example = build_example(my_dir, name, netlist, netlist_setup, constraints)
    run_example(example, n=1, cleanup=False)
