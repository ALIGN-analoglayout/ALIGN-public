from align.schema.types import set_context
import pathlib
import pprint
import json

from .util import _write_circuit_graph
from ..schema.subcircuit import SubCircuit
from ..schema.parser import SpiceParser
from .preprocess import preprocess_stack_parallel
from .create_database import CreateDatabase
from .match_graph import Annotate
from .read_setup import read_setup
from .write_verilog_lef import WriteVerilog
from .find_constraint import FindConst
from .user_const import ConstraintParser
from ..schema import constraint
from ..primitive import generate_primitive_lef
import logging

from align import primitive
logger = logging.getLogger(__name__)

def generate_hierarchy(netlist_path, subckt, output_dir, flatten_heirarchy, pdk_dir, uniform_height):
    config_path =  pathlib.Path(__file__).resolve().parent.parent / 'config'
    ckt_data = compiler_input(netlist_path, subckt, pdk_dir, config_path, flatten_heirarchy)
    return compiler_output(netlist_path, ckt_data, subckt, output_dir, pdk_dir, uniform_height)

def compiler_input(input_ckt:pathlib.Path, design_name:str, pdk_dir:pathlib.Path, config_path: pathlib.Path, flat=0, Debug=False):
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
    #
    # TODO: flatten should be separate pass
    #
    ckt_parser = SpiceParser()
    lib_parser = SpiceParser()
    # Read model file to map devices
    # TODO: add pdk specific model files
    model_statemenets = config_path / 'model.txt'
    with open(model_statemenets) as f:
        lines = f.read()
    ckt_parser.parse(lines)
    lib_parser.parse(lines)

    with open(input_ckt) as f:
        lines =  f.read()
    ckt_parser.parse(lines)

    lib_files = ['basic_template.sp', 'user_template.sp']
    for lib_file in lib_files:
        with open(config_path /lib_file) as f:
            lines = f.read()
        lib_parser.parse(lines)

    library = lib_parser.library
    spath = [cf for cf in input_dir.rglob('*.setup') if cf.stem.upper()==design_name]
    if spath:
        logger.info(f"Reading setup file {spath[0]}")
        design_setup = read_setup(spath[0])
    else:
        logger.info(f"no setup file found for design {design_name} in {input_dir}, other setup files {[cf for cf in input_dir.rglob('*.setup')]}")
        design_setup = read_setup(input_dir/ 'dummy')
    logger.debug(f"template parent path: {pathlib.Path(__file__).parent}")

    primitives = [v for v in library if isinstance(v, SubCircuit) and v.name not in design_setup['DONT_USE_CELLS']]
    #TODO: update the order based on weighing mechanism
    primitives.sort(key=lambda x: len(x.elements) + 1/len(x.nets) + len(set([e.model for e in x.elements])), reverse=True)
    logger.debug(f"dont use cells: {design_setup['DONT_USE_CELLS']}")
    logger.debug(f"all library elements: {[ele.name for ele in primitives]}")
    if len(design_setup['DONT_USE_CELLS'])>0:
        primitives=[v for v in primitives if v.name not in design_setup['DONT_USE_CELLS']]

    #generator will be called for these elments
    with open(pdk_dir /'generators.json') as fp:
        generators = json.load(fp).keys()
    logger.debug(f"Available generator for cells: {generators}")

    if Debug==True:
        _write_circuit_graph(design_name, ckt_parser.library.find(design_name),
                                     "./circuit_graphs/")

    const_parse = ConstraintParser(pdk_dir, input_dir)
    #TODO FLAT implementation
    create_data = CreateDatabase(ckt_parser, const_parse)
    ckt_data= create_data.read_inputs(design_name)
    logger.debug(f"START preprocessing from top {design_name.upper()}")
    preprocess_stack_parallel(ckt_data, design_setup, design_name.upper())

    logger.debug( "\n################### FINAL CIRCUIT AFTER preprocessing #################### \n")
    logger.debug(ckt_parser)
    annotate = Annotate(ckt_data, design_setup, primitives, generators)
    annotate.annotate()
    for ckt in ckt_data:
        if isinstance(ckt, SubCircuit):
            #Check no repeated ports
            assert ckt.pins, f"floating module found {ckt.name}"
            assert len(ckt.pins) == len(set(ckt.pins)), f"duplicate pins found in module {ckt.name}, {ckt.pins}"
            for ele in ckt.elements:
                if isinstance(ckt_data.find(ele.model), SubCircuit):
                    assert len(ele.pins) == len(ckt_data.find(ele.model).pins)
    return ckt_data

def compiler_output(input_ckt, ckt_data, design_name:str, result_dir:pathlib.Path, pdk_dir:pathlib.Path, uniform_height=False):
    """
    search for constraints and write output in verilog format
    Parameters
    ----------
    input_ckt : TYPE. input circuit path
        DESCRIPTION.Used to take designer provided constraints
    library : TYPE. list of library graphs used
        DESCRIPTION.
    ckt_data : TYPE. dict of reduced circuit graph
        DESCRIPTION. this list is used to generate constraints
    design_name : TYPE. name of top level design
        DESCRIPTION.
    result_dir : TYPE. directoy path for writing results
        DESCRIPTION. writes out a verilog netlist, spice file and constraints
    pdk_dir : TYPE. directory path containing pdk layers.json file
        DESCRIPTION. reads design info like cell height,cap size, routing layer from design_config file in config directory
    uniform_height : creates cells of uniform height

    Raises
    ------
    SystemExit: We don't hanadle floating ports in design. They should be removed before hand
        DESCRIPTION.

    Returns
    -------
    primitives : Input parmeters for cell generator
        DESCRIPTION.

    """
    layers_json = pdk_dir / 'layers.json'
    with open(layers_json,"rt") as fp:
        pdk_data=json.load(fp)
    design_config = pdk_data["design_info"]

    if not result_dir.exists():
        result_dir.mkdir()
    logger.debug(f"Writing results in dir: {result_dir} {ckt_data}")
    input_dir = input_ckt.parents[0]

    verilog_tbl = { 'modules': [], 'global_signals': []}
    spath = [cf for cf in input_dir.rglob('*.setup') if cf.stem.upper()==design_name]
    if spath:
        logger.info(f"Reading setup file {spath[0]}")
        design_setup = read_setup(spath[0])
    else:
        design_setup = read_setup(input_dir/ 'dummy')
    try:
        POWER_PINS = [design_setup['GND'][0],design_setup['POWER'][0]]
    except (IndexError, ValueError):
        POWER_PINS = []
        logger.info("Power and ground nets not found. Power grid will not be constructed.")

    #read lef to not write those modules as macros
    with open(pdk_dir /'generators.json') as fp:
        generators = json.load(fp)
    logger.debug(f"Available library cells: {', '.join(generators.keys())}")

    primitives = {}
    for ckt in ckt_data:
        if not isinstance(ckt, SubCircuit):
            continue
        logger.debug(f"Found module: {ckt.name} {ckt.elements} {ckt.pins}")
        for const in ckt.constraints:
            if isinstance(const, constraint.GuardRing):
                primitives['guard_ring'] = {'primitive':'guard_ring'}
            if isinstance(const, constraint.GroupCaps):
                primitives[const.unit_cap.upper()] = {'primitive': 'cap', 'value':int(const.unit_cap.split('_')[1].replace('f',''))}

        for ele in ckt.elements:
            primitive_generator = ele.generator
            assert 'generic' in generators
            if primitive_generator in generators:
                generators[str(ele.model)] = primitive_generator
                assert generate_primitive_lef(ele, primitive_generator, generators, primitives, design_config, uniform_height)
            else:
                ele.add_abs_name(ele.generator)
                logger.debug(f"No physical information found for: {ele.name} of type : {ele.model}")
        logger.debug(f"generated data for {ele.name} : {pprint.pformat(primitives, indent=4)}")
    logger.debug(f"All available cell generator with updates: {generators}")
    for ckt in ckt_data:
        if not isinstance(ckt, SubCircuit):
            continue
        if ckt.name not in  generators:
            ## Removing constraints to fix cascoded cmc
            if ckt.name not in design_setup['DIGITAL']:
                logger.debug(f"call constraint generator writer for block: {ckt.name}")
                stop_points = design_setup['POWER'] + design_setup['GND'] + design_setup['CLOCK']
                if ckt.name not in design_setup['NO_CONST']:
                    FindConst(ckt_data, ckt.name, stop_points)

            ## Write out modified netlist & constraints as JSON
            logger.debug(f"call verilog writer for block: {ckt.name}")
            wv = WriteVerilog(ckt, ckt_data, POWER_PINS)
            verilog_tbl['modules'].append( wv.gen_dict())
    if len(POWER_PINS)>0:
        for i, nm in enumerate(POWER_PINS):
            verilog_tbl['global_signals'].append( { 'prefix' :'global_power', 'formal' : f'supply{i}', 'actual' : nm})

    with (result_dir / f'{design_name.upper()}.verilog.json').open( 'wt') as fp:
        json.dump( verilog_tbl, fp=fp, indent=2)

    logger.info("Completed topology identification.")
    logger.debug(f"OUTPUT verilog json netlist at: {result_dir}/{design_name.upper()}.verilog.json")
    logger.debug(f"OUTPUT const file at: {result_dir}/{design_name.upper()}.pnr.const.json")
    return primitives
