import pathlib
import pprint
import json

from .util import _write_circuit_graph, max_connectivity
from align.schema.subcircuit import SubCircuit
from align.schema.parser import SpiceParser
from .preprocess import define_SD, preprocess_stack_parallel, remove_pg_pins
from .create_database import CreateDatabase
from .match_graph import Annotate
from .read_setup import read_setup
from .write_verilog_lef import write_verilog, WriteVerilog, generate_lef
from .common_centroid_cap_constraint import CapConst
from .find_constraint import FindConst
from .user_const import ConstraintParser
from ..schema import constraint
from ..schema.hacks import HierDictNode
from ..schema.graph import Graph
import logging
logger = logging.getLogger(__name__)

def generate_hierarchy(netlist_path, subckt, output_dir, flatten_heirarchy, pdk_dir, uniform_height):
    config_path =  pathlib.Path(__file__).resolve().parent.parent / 'config'
    ckt_data = compiler(netlist_path, subckt, pdk_dir, config_path, flatten_heirarchy)
    return compiler_output(netlist_path, ckt_data, subckt, output_dir, pdk_dir, uniform_height)

def compiler(input_ckt:pathlib.Path, design_name:str, pdk_dir:pathlib.Path, config_path: pathlib.Path, flat=0, Debug=False):
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
    design_name = design_name.upper()
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
    logger.debug(f"all library elements {library}")

    design_setup = read_setup(input_dir / f'{design_name}.setup')
    logger.debug(f"template parent path: {pathlib.Path(__file__).parent}")

    primitives = [v for v in library if isinstance(v, SubCircuit) and v.name not in design_setup['DONT_USE_CELLS']]
    #TODO: Future improvement
    primitives.sort(key=lambda x: len(x.elements) + len(x.nets), reverse=True)
    logger.debug(f"dont use cells: {design_setup['DONT_USE_CELLS']}")
    logger.debug(f"all library elements: {[ele.name for ele in primitives]}")
    if len(design_setup['DONT_USE_CELLS'])>0:
        primitives=[v for v in primitives if v.name not in design_setup['DONT_USE_CELLS']]

    #read generator will be called for these elments
    with open(pdk_dir /'generators.json') as fp:
        generators = json.load(fp).keys()
    logger.debug(f"Available generator for cells: {generators}")

    if Debug==True:
        _write_circuit_graph(design_name, Graph(ckt_parser.library.find(design_name)),
                                     "./circuit_graphs/")

    const_parse = ConstraintParser(pdk_dir, input_dir)
    #TODO FLAT implementation
    create_data = CreateDatabase(ckt_parser, const_parse)
    ckt_data= create_data.read_inputs(design_name)
    logger.debug("START preprocessing")

    stacked_subcircuit=[]
    # TODO: Re-implement stacked transistor detection using new passes

    for ckt in ckt_data:
        if isinstance(ckt, SubCircuit):
            logger.debug(f"preprocessing circuit name: {ckt}")
            if ckt.name not in design_setup['DIGITAL']:
                define_SD(ckt,design_setup['POWER'],design_setup['GND'], design_setup['CLOCK'])
                stacked_subcircuit.append(preprocess_stack_parallel(ckt_parser,ckt_data,ckt.name))
    for circuit_name in stacked_subcircuit:
        if circuit_name in ckt_data.keys() and circuit_name is not design_name:
            logger.debug(f"removing stacked subcircuit {circuit_name}")
            del ckt_data[circuit_name]

    # TODO: pg_pins should be marked using constraints. Not manipulating netlist
    #
    logger.debug("Modifying pg pins in design for PnR")
    pg_pins = design_setup['POWER']+design_setup['GND']
    # remove_pg_pins(ckt_data,design_name, pg_pins) TBD

    logger.debug( "\n################### FINAL CIRCUIT AFTER preprocessing #################### \n")
    logger.debug(ckt_parser)
    # for circuit in ckt_data.values():
    #     for node in circuit["graph"].nodes(data=True):
    #         if node[1]["inst_type"]!='net':
    #             logger.debug(node)
    #print(ckt_data)
    # print(primitives)
    annotate = Annotate(ckt_data, design_setup, primitives, generators)
    annotate.annotate()
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

    design_setup = read_setup(input_dir / (design_name + '.setup'))
    try:
        POWER_PINS = [design_setup['GND'][0],design_setup['POWER'][0]]
    except (IndexError, ValueError):
        POWER_PINS = []
        logger.error("no power and gnd defination, correct setup file")

    #read lef to not write those modules as macros
    lef_path = pathlib.Path(__file__).resolve().parent.parent / 'config'
    with open(pdk_dir /'generators.json') as fp:
        generators = json.load(fp).keys()
    logger.debug(f"Available library cells: {', '.join(generators)}")

    primitives = {}
    for ckt in ckt_data:
        if not isinstance(ckt, SubCircuit):
            continue
        logger.debug(f"Found module: {ckt.name} {ckt.elements}")
        # constraints = member["constraints"]

        # for const in constraints:
        #     if isinstance(const, constraint.GuardRing):
        #         primitives['guard_ring'] = {'primitive':'guard_ring'}

        # logger.debug(f"Reading nodes from graph: {name}")
        for ele in ckt.elements:
            #Dropping floating ports
            lef_name = ele.model
            print(lef_name)
            if lef_name in generators:
                subckt= ckt_data.find(lef_name)
                block_name, block_args = generate_lef(ele, subckt,generators, design_config, uniform_height)
                #block_name_ext = block_name.replace(lef_name,'')
                logger.debug(f"Created new lef for: {block_name} {lef_name}")
                #Multiple instances of same module
                # if 'inst_copy' in attr:
                #     for nm in list(ckt_data.keys()):
                #         if nm == lef_name + attr['inst_copy']:
                #             if block_name not in ckt_data.keys():
                #                 logger.warning('Trying to modify a dictionary while iterating over it!')
                #                 ckt_data[block_name] = ckt_data.pop(nm)
                #             else:
                #                 #For cells with extra parameters than current primitive naming convention
                #                 generators.append(nm)
                #     graph.nodes[node]["inst_type"] = block_name
                #     generators.append(block_name)

                # Only unit caps are generated
                # if  block_name.lower().startswith('cap'):
                #     graph.nodes[node]['inst_type'] = block_args['primitive']
                #     block_args['primitive'] = block_name
                # else:
                #     graph.nodes[node]['inst_type'] = block_name

                if block_name in primitives:
                    if block_args != primitives[block_name]:
                        logging.warning(f"two different primitve {block_name} of size {primitives[block_name]} {block_args}got approximated to same unit size")
                else:
                    primitives[block_name] = block_args
            # elif "values" in attr and 'inst_copy' in attr:
            #     member["graph"].nodes[node]["inst_type"]= lef_name + attr["inst_copy"]
            #     generators.append(block_name)

            else:
                logger.debug(f"No physical information found for: {ele.name}")
        logger.debug(f"generated data for {ele.name} : {pprint.pformat(primitives, indent=4)}")
    logger.debug(f"All available cell generator with updates: {generators}")
    for ckt in ckt_data:
        if not isinstance(ckt, SubCircuit):
            continue
        # graph = member["graph"]
        # logger.debug(f"Found module: {name} {graph.nodes()}")
        # inoutpin = []
        # floating_ports=[]
        # if "ports_match" in member and member["ports_match"]:
        #     for key in member["ports_match"].keys():
        #         if key not in POWER_PINS:
        #             inoutpin.append(key)
        #     if member["ports"]:
        #         logger.debug(f'Found module ports: {member["ports"]} {member["name"]}')
        #         floating_ports = set(inoutpin) - set(member["ports"]) - set(design_setup['POWER']) -set(design_setup['GND'])
        #         if len(list(floating_ports))> 0:
        #             logger.error(f"floating ports found: {name} {floating_ports}")
        #             raise SystemExit('Please remove floating ports')
        # else:
        #     inoutpin = member["ports"]
        if ckt.name not in  generators:

            ## Removing constraints to fix cascoded cmc
            if ckt.name not in design_setup['DIGITAL']:
                logger.debug(f"call constraint generator writer for block: {ckt.name}")
                stop_points = design_setup['POWER'] + design_setup['GND'] + design_setup['CLOCK']
                constraints = ckt.constraints
                # if ckt.name not in design_setup['NO_CONST']:
                #     constraints = FindConst(graph, name, inoutpin, member["ports_weight"], constraints, stop_points)
                # constraints = CapConst(graph, name, design_config["unit_size_cap"], constraints, design_setup['MERGE_SYMM_CAPS'])
                # ckt_data[name] = ckt_data[name].copy(
                #     update={'constraints': constraints}
                # )
            ## Write out modified netlist & constraints as JSON
            logger.debug(f"call verilog writer for block: {ckt.name}")
            wv = WriteVerilog(ckt.name, ckt.pins, ckt_data, POWER_PINS)
            verilog_tbl['modules'].append( wv.gen_dict())
    if len(POWER_PINS)>0:
        for i, nm in enumerate(POWER_PINS):
            verilog_tbl['global_signals'].append( { 'prefix' :'global_power', 'formal' : f'supply{i}', 'actual' : nm})

    with (result_dir / f'{design_name}.verilog.json').open( 'wt') as fp:
        json.dump( verilog_tbl, fp=fp, indent=2)

    with (result_dir / f'{design_name}.v').open( 'wt') as fp:
        write_verilog( verilog_tbl, fp)

    logger.info("Topology identification done !!!")
    logger.info(f"OUTPUT verilog json netlist at: {result_dir}/{design_name}.verilog.json")
    logger.info(f"OUTPUT verilog netlist at: {result_dir}/{design_name}.v")
    logger.info(f"OUTPUT const file at: {result_dir}/{design_name}.pnr.const.json")
    exit()
    return primitives
