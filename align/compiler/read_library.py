import pathlib
from ..schema.parser import SpiceParser
from ..schema.subcircuit import SubCircuit
import logging
from ..schema.library import Library
from align.primitive.main import get_generator


logger = logging.getLogger(__name__)


def read_models(pdk_dir: pathlib.Path, config_path=None):

    pdk_models = get_generator('pdk_models', pdk_dir)
    library = Library(loadbuiltins=True, pdk_models=pdk_models)
    ckt_parser = SpiceParser(library=library)
    # Read model file to map devices
    if config_path is None:
        config_path = pathlib.Path(__file__).resolve().parent.parent / "config"

    model_statements = pdk_dir / "models.sp"

    if not model_statements.exists():
        if not pdk_dir.exists():
            logger.warning(f"Missing pdk directory for reading model {pdk_dir} ")
        else:
            logger.warning(f"Missing models.sp file in PDK directory {model_statements}")
        model_statements = config_path / "models.sp"

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

    lib_files = ["basic_template.sp", "user_template.sp"]
    for lib_file in lib_files:
        lib_file_path = pdk_dir/lib_file
        if not lib_file_path.exists():
            lib_file_path = config_path / lib_file
        with open(lib_file_path) as f:
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
