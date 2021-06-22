import pytest
try:
    from .helper import *
    from . import circuits
except:
    from helper import *
    import circuits


def test_comparator_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    ckt_setup = f"""POWER = vccx\nGND = vssx"""
    ckt_const = """[]"""
    example = build_example(my_dir, name, netlist, ckt_setup, ckt_const)
    run_example(example, n=1)


def test_ota_six_1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    ckt_setup = f"""POWER = vccx\nGND = vssx"""
    ckt_const = """[]"""
    example = build_example(my_dir, name, netlist, ckt_setup, ckt_const)
    run_example(example, n=1)

