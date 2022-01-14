import pathlib
from ..schema.parser import SpiceParser
from ..schema.subcircuit import SubCircuit
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

    logger.info(f"Using model file from {config_path}")
    with open(model_statements, 'r') as f:
        lines = f.read()
    ckt_parser.parse(lines)
    return ckt_parser


def read_lib(pdk_dir: pathlib.Path,  config_path=None):
    # Read model file to map devices

    lib_parser = read_models(pdk_dir)
    if config_path is None:
        config_path = pathlib.Path(__file__).resolve().parent.parent / "config"

    lib_files = ["basic_template.sp", "user_template.sp"]
    for lib_file in lib_files:
        with open(config_path / lib_file) as f:
            lines = f.read()
        lib_parser.parse(lines)

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
