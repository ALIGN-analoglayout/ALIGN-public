import pathlib
import pprint
import json

from ..schema.subcircuit import SubCircuit, Model
from ..schema import constraint
from .preprocess import preprocess_stack_parallel
from .create_database import CreateDatabase
from .read_library import read_lib, read_models, order_lib
from .match_graph import Annotate
from .write_verilog_lef import WriteVerilog
from .find_constraint import FindConst
from .user_const import ConstraintParser
from ..primitive import generate_primitive_lef
import logging


logger = logging.getLogger(__name__)


def generate_hierarchy(
    netlist_path: pathlib.Path,
    design_name: str,
    output_dir: pathlib.Path,
    flatten_heirarchy: bool,
    pdk_dir: pathlib.Path,
    uniform_height: bool
):
    config_path = pathlib.Path(__file__).resolve().parent.parent / "config"
    ckt_data = compiler_input(
        netlist_path,
        design_name,
        pdk_dir,
        config_path,
        flatten_heirarchy
    )
    primitives = call_primitive_generator(
        ckt_data,
        pdk_dir,
        uniform_height
    )
    verilog_tbl = constraint_generator(
        ckt_data
    )
    compiler_output(
        ckt_data,
        design_name,
        verilog_tbl,
        output_dir,
    )
    return primitives, ckt_data


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
    primitives = order_lib(library)

    const_parse = ConstraintParser(pdk_dir, input_dir)
    # TODO FLAT implementation
    create_data = CreateDatabase(ckt_parser, const_parse)
    ckt_data = create_data.read_inputs(design_name)
    create_data.add_generators(pdk_dir)
    logger.debug(f"START preprocessing from top {design_name.upper()}")
    preprocess_stack_parallel(ckt_data, design_name.upper())

    logger.debug("\n###### FINAL CIRCUIT AFTER preprocessing ###### \n")
    logger.debug(ckt_parser)
    annotate = Annotate(ckt_data, primitives)
    annotate.annotate()
    for ckt in ckt_data:
        if isinstance(ckt, SubCircuit):
            assert ckt.pins, f"floating module found {ckt.name}"
            assert len(ckt.pins) == len(
                set(ckt.pins)
            ), f"duplicate pins found in module {ckt.name}, {ckt.pins}"
            for ele in ckt.elements:
                if isinstance(ckt_data.find(ele.model), SubCircuit):
                    assert len(ele.pins) == len(ckt_data.find(ele.model).pins), "incorrect subckt instantiation"
    return ckt_data


def call_primitive_generator(
    ckt_data,
    pdk_dir: pathlib.Path,
    uniform_height=False
):
    """call_primitive_generator [summary]

    [extended_summary]

    Args:
        ckt_data ([type]): ckt library after annotation
        pdk_dir (pathlib.Path):  directory path containing pdk layers.json file
        DESCRIPTION. reads design info like cell height,cap size, routing layer from design_config file in config directory
        uniform_height (bool, optional): creates cells of uniform height. Defaults to False.

    Returns:
        primitives, list of generated primitives
    """
    layers_json = pdk_dir / "layers.json"
    with open(layers_json, "rt") as fp:
        pdk_data = json.load(fp)
    design_config = pdk_data["design_info"]
    # read lef to not write those modules as macros
    primitives = {}
    for ckt in ckt_data:
        if not isinstance(ckt, SubCircuit):
            continue
        elif [True for const in ckt.constraints if isinstance(const, constraint.Generator)]:
            continue
        logger.debug(f"Found module: {ckt.name} {ckt.elements} {ckt.pins}")
        group_cap_instances = []
        for const in ckt.constraints:
            if isinstance(const, constraint.GuardRing):
                primitives["guard_ring"] = {"primitive": "guard_ring"}
            if isinstance(const, constraint.GroupCaps):
                primitives[const.unit_cap.upper()] = {
                    "primitive": "cap",
                    "value": int(const.unit_cap.split("_")[1].replace("f", "")),
                }
                group_cap_instances.append(const.name.upper())

        for ele in ckt.elements:
            # Three types of elements can exist:
            # ele can be a model ele can be model defined in models.sp/base model
            # ele can be a subcircuit with a generator associated
            # ele can be a sucircuit with no generator, PnR will place and route this instance
            generator = ckt_data.find(ele.generator)
            logger.debug(f"element {ele.name} generator {ele.generator} generator properties {generator}")
            if ele.name in group_cap_instances:
                ele.add_abs_name(ele.model)
            elif isinstance(generator, SubCircuit):
                gen_const = [True for const in generator.constraints if isinstance(const, constraint.Generator)]
                if gen_const:
                    assert generate_primitive_lef(
                        ele,
                        primitives,
                        design_config,
                        uniform_height,
                        pdk_dir
                    )
                else:
                    ele.add_abs_name(ele.model)
                    logger.info(
                        f"No physical information found for: {ele.name} of type : {ele.model}"
                    )
            elif generator is None or isinstance(generator, Model):
                assert generate_primitive_lef(
                    ele,
                    primitives,
                    design_config,
                    uniform_height,
                    pdk_dir
                )
            else:
                assert False, f"No definition found for instance {ele} in {ckt.name}"
        logger.debug(
            f"generated data for {ele.name} : {pprint.pformat(primitives, indent=4)}"
        )

    return primitives


def constraint_generator(ckt_data):
    """
    search for constraints and
    Args:
        ckt_data : ckt library after annotation
        design_name : name of top level design
        result_dir : directoy path for writing results

    """

    verilog_tbl = {"modules": [], "global_signals": []}

    for subckt in ckt_data:
        if not isinstance(subckt, SubCircuit):
            continue
        gen_const = [True for const in subckt.constraints if isinstance(const, constraint.Generator)]
        if not gen_const:
            FindConst(subckt)
            # Create modified netlist & constraints as JSON
            logger.debug(f"call verilog writer for block: {subckt.name}")
            wv = WriteVerilog(subckt, ckt_data)
            verilog_tbl["modules"].append(wv.gen_dict())
    return verilog_tbl


def compiler_output(
    ckt_data,
    design_name: str,
    verilog_tbl: dict,
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
