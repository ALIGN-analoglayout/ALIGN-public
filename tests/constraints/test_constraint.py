try:
    from .utils import get_test_id, build_example, run_example
    from . import circuits
except BaseException:
    from utils import get_test_id, build_example, run_example
    import circuits


def test_aspect_ratio_low():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    setup = ""
    constraints = [{"constraint": "AspectRatio", "subcircuit": "example_aspect_ratio_min", "ratio_low": 3}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_aspect_ratio_high():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    setup = ""
    constraints = [{"constraint": "AspectRatio", "subcircuit": "example_aspect_ratio_max", "ratio_high": 1}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_boundary_max_width():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    setup = ""
    constraints = [{"constraint": "Boundary", "subcircuit": "example_boundary_max_width", "max_width": 3.5}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_boundary_max_height():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.cascode_amplifier(name)
    setup = ""
    constraints = [{"constraint": "Boundary", "subcircuit": "example_boundary_max_height", "max_height": 1.3}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example)


def test_do_not_identify():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.ota_five(name)
    setup = ""
    constraints = [{"constraint": "AlignInOrder", "line": "left", "instances": ["mp1", "mn1"]}]
    example = build_example(name, netlist, setup, constraints)
    run_example(example)
