import pathlib

from align.schema.types import set_context
from ..schema.parser import SpiceParser
from ..schema.subcircuit import SubCircuit
from ..schema import constraint
from ..primitive import main

import logging


logger = logging.getLogger(__name__)


def read_models(pdk_dir: pathlib.Path, config_path=None):
    ckt_parser = SpiceParser()
    # Read model file to map devices
    if config_path is None:
        config_path = pathlib.Path(__file__).resolve().parent.parent / "config"

    model_statements = pdk_dir / "models.sp"

    if not model_statements.exists():
        model_statements = config_path / "models.sp"
        assert model_statements.exists(), f"Missing models.sp file in PDK directory {model_statements}"

    logger.info(f"Using model file from {model_statements}")
    with open(model_statements, 'r') as f:
        lines = f.read()
    ckt_parser.parse(lines)
    return ckt_parser


def read_lib(pdk_dir: pathlib.Path,  config_path=None):
    # Read model file to map devices

    lib_parser = read_models(pdk_dir)
    if config_path is None:
        config_path = pathlib.Path(__file__).resolve().parent.parent / "config"
        assert config_path.exists(), f"Missing config path {config_path}"

    lib_files = ["basic_template.sp", "user_template.sp"]
    for lib_file in lib_files:
        with open(config_path / lib_file) as f:
            lines = f.read()
        lib_parser.parse(lines)
    for subckt in lib_parser.library:
        if isinstance(subckt, SubCircuit):
            if main.get_generator(subckt.name, pdk_dir) and \
                    not [True for const in subckt.constraints if isinstance(const, constraint.Generator)]:
                # TODO: In future can we overwrite subcircuit based on user constraint

                with set_context(subckt.constraints):
                    subckt.constraints.append(constraint.Generator())

    return lib_parser.library


def order_lib(library):
    primitives = [
        v for v in library
        if isinstance(v, SubCircuit)
    ]
    # TODO: update the order based on weighing mechanism
    primitives.sort(
        key=lambda x: (len(x.elements),
                       1 / len(x.nets),
                       len(set([e.model for e in x.elements]))),
        reverse=True,
    )
    logger.debug(f"all library elements: {[ele.name for ele in primitives]}")

    return primitives
