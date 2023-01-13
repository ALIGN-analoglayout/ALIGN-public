import os
import logging

from . import circuits
from .utils import get_test_id, build_example, run_example

logger = logging.getLogger(__name__)

CLEANUP = False if os.getenv("CLEANUP", None) else True
LOG_LEVEL = os.getenv("LOG_LEVEL", "INFO")


def test_common_source():
    name = f'ckt_{get_test_id()}'
    netlist = circuits.common_source(name)
    constraints = [
        {"constraint": "PowerPorts", "ports": ["vccx"]},
        {"constraint": "GroundPorts", "ports": ["vssx"]},
        {"constraint": "AlignInOrder", "line": "left", "instances": ["mp0", "mn0"]}
    ]
    example = build_example(name, netlist, constraints)
    run_example(example, cleanup=CLEANUP, log_level=LOG_LEVEL, additional_args=['--placer', 'python'])
