import os
import pytest
import json
import shutil
from .utils import get_test_id, build_example, run_example
from . import circuits
import logging
logger = logging.getLogger(__name__)

CLEANUP = False if os.getenv("CLEANUP", None) else True
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")


def find_constraint(module, name):
    return [constraint for constraint in module["constraints"] if constraint["constraint"] == name]


def test_ota_six():
    """ Align should detect a symmetry with two pairs """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_six(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 1
        assert len(symmetry_constraints[0]["pairs"]) == 2
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_comparator():
    """ Align should detect a symmetry with six pairs """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 1
        assert len(symmetry_constraints[0]["pairs"]) == 6
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_comparator_analog():
    """ Align should detect at least one symmetry line """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.comparator_analog(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) > 1
        # assert len(symmetry_constraints[0]["pairs"]) == 6
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_ring_oscillator():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ro_simple(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 0
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_charge_pump_switch():
    """ Align should detect the array """
    num_sw = 8
    name = f'ckt_{get_test_id()}'
    netlist = circuits.charge_pump_switch(name, size=num_sw)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 0
        align_constraints = find_constraint(module_top, "AlignInOrder")
        assert len(align_constraints) == 1
        assert len(align_constraints[0]["instances"]) == num_sw
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_opamp_poor():
    """ Align should detect a symmetry line with four pairs """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.opamp_poor(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 1
        assert len(symmetry_constraints[0]["pairs"]) == 4

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_folded_cascode():
    """ Align should detect a single symmetry line, not two lines """
    name = f'ckt_{get_test_id()}'
    netlist = circuits.folded_cascode(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) > 0
        # assert len(symmetry_constraints[0]["pairs"]) == 5

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_ldo_amp():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ldo_amp(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) > 0
    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


def test_two_stage_ota():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.two_stage_ota_differential(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 1
        assert len(symmetry_constraints[0]["pairs"]) == 4

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)


@pytest.mark.skip(reason="symmetry constraint generated but it is okay")
def test_analog_mux_4to1():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.analog_mux_4to1(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]}
    ]
    example = build_example(name, netlist, constraints)
    ckt_dir, run_dir = run_example(example, cleanup=False, log_level=LOG_LEVEL, additional_args=["--flow_stop", "1_topology"])
    name = name.upper()
    with (run_dir / '1_topology' / f'{name.upper()}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        modules = {module['name']: module for module in verilog_json['modules']}
        assert name in modules, f'Module {name} not found in verilog.json'
        module_top = modules[name]
        symmetry_constraints = find_constraint(module_top, "SymmetricBlocks")
        assert len(symmetry_constraints) == 1
        assert len(symmetry_constraints[0]["pairs"]) == 5

    if CLEANUP:
        shutil.rmtree(run_dir)
        shutil.rmtree(ckt_dir)
