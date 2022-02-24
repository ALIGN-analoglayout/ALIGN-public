import pathlib
import json

from align import primitive

from ..schema import SubCircuit, constraint
from .preprocess import preprocess_stack_parallel
from .create_database import CreateDatabase
from .read_library import read_lib, read_models, order_lib
from .match_graph import Annotate
from .write_verilog_lef import WriteVerilog
from .find_constraint import constraint_generator
from .user_const import ConstraintParser
from .gen_abstract_name import PrimitiveLibrary
import logging


logger = logging.getLogger(__name__)


def generate_hierarchy(
    netlist_path: pathlib.Path,
    design_name: str,
    output_dir: pathlib.Path,
    flatten_heirarchy: bool,
    pdk_dir: pathlib.Path
):
    config_path = pathlib.Path(__file__).resolve().parent.parent / "config"
    ckt_data, primitive_library = compiler_input(
        netlist_path,
        design_name,
        pdk_dir,
        config_path,
        flatten_heirarchy
    )
    annotate_library(ckt_data, primitive_library)
    primitives = PrimitiveLibrary(ckt_data, pdk_dir).gen_primitive_collateral()
    constraint_generator(ckt_data)
    compiler_output(ckt_data, design_name, output_dir)
    return primitives

def compiler_input(
    input_ckt: pathlib.Path,
    design_name: str,
    pdk_dir: pathlib.Path,
    config_path: pathlib.Path,
    flat=0,
    Debug=False,
):
    """
    Reads input spice file, converts to a graph format and create hierarchies in the graph

    Parameters
    ----------
    input_ckt : input circuit path
        DESCRIPTION.
    design_name : name of top level subckt in design
        DESCRIPTION.
    flat : TYPE, flat/hierarchical
        DESCRIPTION. The default is 0.
    Debug : TYPE, writes output graph for debug
        DESCRIPTION. The default is False.

    Returns
    -------
    updated_ckt_list : list of reduced graphs for each subckt
        DESCRIPTION. reduced graphs are subckts after identification of hierarchies
    library : TYPE, list of library graphs
        DESCRIPTION.libraries are used to create hierarchies

    """
    logger.info("Starting topology identification...")
    input_dir = input_ckt.parents[0]
    logger.debug(f"Reading subckt {input_ckt}")
    # TODO: flatten should be separate pass

    ckt_parser = read_models(pdk_dir, config_path)

    with open(input_ckt) as f:
        lines = f.read()
    ckt_parser.parse(lines)

    library = read_lib(pdk_dir, config_path)
    primitive_library = order_lib(library)

    const_parse = ConstraintParser(pdk_dir, input_dir)
    # TODO FLAT implementation
    create_data = CreateDatabase(ckt_parser, const_parse)
    ckt_data = create_data.read_inputs(design_name)
    create_data.add_generators(pdk_dir)
    logger.debug(f"START preprocessing from top {design_name.upper()}")
    preprocess_stack_parallel(ckt_data, design_name.upper())

    logger.debug("\n###### FINAL CIRCUIT AFTER preprocessing ###### \n")
    logger.debug(ckt_parser)
    return ckt_data, primitive_library


def annotate_library(ckt_data, primitive_library):
    at = Annotate(ckt_data, primitive_library)
    at.annotate()
    for ckt in ckt_data:
        if isinstance(ckt, SubCircuit):
            assert ckt.pins, f"floating module found {ckt.name}"
            assert len(ckt.pins) == len(
                set(ckt.pins)
            ), f"duplicate pins found in module {ckt.name}, {ckt.pins}"
            for ele in ckt.elements:
                if isinstance(ckt_data.find(ele.model), SubCircuit):
                    assert len(ele.pins) == len(ckt_data.find(ele.model).pins), "incorrect subckt instantiation"


def compiler_output(
    ckt_data,
    design_name: str,
    result_dir: pathlib.Path,
):
    """compiler_output: write output in verilog format
    Args:
        ckt_data : annotated ckt library  and constraint
        design_name : name of top level design
        verilog_tbl (dict): verilog dict for PnR
        result_dir : directoy path for writing results
    """
    top_ckt = ckt_data.find(design_name)
    assert top_ckt, f"design {top_ckt} not found in database"

    verilog_tbl = {"modules": [], "global_signals": []}

    for subckt in ckt_data:
        if not isinstance(subckt, SubCircuit):
            continue
        gen_const = [True for const in subckt.constraints if isinstance(const, constraint.Generator)]
        if not gen_const:
            # Create modified netlist
            logger.debug(f"call verilog writer for block: {subckt.name}")
            wv = WriteVerilog(subckt, ckt_data)
            verilog_tbl["modules"].append(wv.gen_dict())

    power_ports = list()
    ground_ports = list()
    for const in top_ckt.constraints:
        if isinstance(const, constraint.PowerPorts):
            power_ports.extend(const.ports)
        elif isinstance(const, constraint.GroundPorts):
            ground_ports.extend(const.ports)
    try:
        pg_grid = [ground_ports[0], power_ports[0]]
    except (IndexError, ValueError):
        pg_grid = list()
        logger.info(
            "Power and ground nets not found. Power grid will not be constructed."
        )
    if len(pg_grid) > 0:
        for i, nm in enumerate(pg_grid):
            verilog_tbl["global_signals"].append(
                {"prefix": "global_power",
                 "formal": f"supply{i}",
                 "actual": nm}
            )

    if not result_dir.exists():
        result_dir.mkdir()
    logger.debug(f"Writing results in dir: {result_dir} {ckt_data}")
    with (result_dir / f"{design_name.upper()}.verilog.json").open("wt") as fp:
        json.dump(verilog_tbl, fp=fp, indent=2)

    logger.info("Completed topology identification.")
    results_path = result_dir/design_name.upper()
    logger.debug(f"OUTPUT verilog json netlist at: {results_path}.verilog.json")
    logger.debug(f"OUTPUT const file at: {results_path}.pnr.const.json")
