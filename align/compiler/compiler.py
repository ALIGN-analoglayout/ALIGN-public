import pathlib
import pprint
import json

from .util import _write_circuit_graph, max_connectivity
from .read_netlist import SpiceParser
from .preprocess import define_SD, preprocess_stack_parallel, remove_pg_pins
from .create_database import CreateDatabase
from .match_graph import Annotate
from .read_setup import read_setup
from .write_verilog_lef import WriteVerilog, print_globals,print_header,generate_lef
from .common_centroid_cap_constraint import WriteCap, check_common_centroid
from .write_constraint import WriteConst, CopyConstFile
from .read_lef import read_lef
from .user_const import ConstraintParser

import logging
logger = logging.getLogger(__name__)

def generate_hierarchy(netlist, subckt, output_dir, flatten_heirarchy, pdk_dir, uniform_height):
    updated_ckt_list,library = compiler(netlist, subckt, pdk_dir, flatten_heirarchy)
    return compiler_output(netlist, library, updated_ckt_list, subckt, output_dir, pdk_dir, uniform_height)

def compiler(input_ckt:pathlib.Path, design_name:str, pdk_dir:pathlib.Path,flat=0,Debug=False):
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
    input_dir=input_ckt.parents[0]
    logger.debug(f"Reading subckt {input_ckt}")
    sp = SpiceParser(input_ckt, design_name, flat)
    circuit_graphs = sp.sp_parser()
    assert circuit_graphs !=None  , f"No subcircuit with name {design_name} found in spice {input_ckt}"
    circuit = circuit_graphs[0]

    design_setup=read_setup(input_dir / f'{input_ckt.stem}.setup')
    logger.debug(f"template parent path: {pathlib.Path(__file__).parent}")
    lib_path=pathlib.Path(__file__).resolve().parent.parent / 'config' / 'basic_template.sp'
    logger.debug(f"template library path: {lib_path}")
    basic_lib = SpiceParser(lib_path)
    library = basic_lib.sp_parser()
    lib_path=pathlib.Path(__file__).resolve().parent.parent / 'config' / 'user_template.sp'
    user_lib = SpiceParser(lib_path)
    library += user_lib.sp_parser()
    library=sorted(library, key=lambda k: max_connectivity(k["graph"]), reverse=True)

    logger.debug(f"dont use cells: {design_setup['DONT_USE_CELLS']}")
    logger.debug(f"all library elements: {[ele['name'] for ele in library]}")
    if len(design_setup['DONT_USE_CELLS'])>0:
        library=[lib_ele for lib_ele in library if lib_ele['name'] not in design_setup['DONT_USE_CELLS']]
    #read lef to not write those modules as macros
    lef_path = pathlib.Path(__file__).resolve().parent.parent / 'config'
    all_lef = read_lef(lef_path)
    logger.debug(f"Available library cells: {', '.join(all_lef)}")

    if Debug==True:
        _write_circuit_graph(circuit["name"], circuit["graph"],
                                     "./circuit_graphs/")
        for lib_circuit in library:
            _write_circuit_graph(lib_circuit["name"], lib_circuit["graph"],
                                         "./circuit_graphs/")
    #Converting graph to dict
    const_parse = ConstraintParser(pdk_dir, input_dir)
    create_data = CreateDatabase(circuit["graph"],const_parse)
    hier_graph_dict = create_data.read_inputs(circuit["name"])

    #remove pg_pins requirement by pnr
    logger.debug("Modifying pg pins in design for PnR")
    pg_pins = design_setup['POWER']+design_setup['GND']
    remove_pg_pins(hier_graph_dict,design_name, pg_pins)

    logger.debug("START preprocessing")
    stacked_subcircuit=[]
    for circuit_name, circuit in hier_graph_dict.items():
        logger.debug(f"preprocessing circuit name: {circuit_name}")
        G1 = circuit["graph"]
        if circuit_name not in design_setup['DIGITAL']:
            define_SD(G1,design_setup['POWER'],design_setup['GND'], design_setup['CLOCK'])
            stacked_subcircuit.append(preprocess_stack_parallel(hier_graph_dict,circuit_name,G1))
    for circuit_name in stacked_subcircuit:
        if circuit_name in hier_graph_dict.keys() and circuit_name is not design_name:
            logger.debug(f"removing stacked subcircuit {circuit_name}")
            del hier_graph_dict[circuit_name]

    logger.debug( "\n################### FINAL CIRCUIT AFTER preprocessing #################### \n")
    for circuit in hier_graph_dict.values():
        for node in circuit["graph"].nodes(data=True):
            if node[1]["inst_type"]!='net':
                logger.debug(node)

    annotate =Annotate(hier_graph_dict, design_setup,library,all_lef)
    updated_ckt_list,lib_names =annotate.annotate()

    return updated_ckt_list, lib_names

def compiler_output(input_ckt, lib_names , updated_ckt_list, design_name:str, result_dir:pathlib.Path, pdk_dir:pathlib.Path, uniform_height=False):
    """
    search for constraints and write output in verilog format
    Parameters
    ----------
    input_ckt : TYPE. input circuit path
        DESCRIPTION.Used to take designer provided constraints
    library : TYPE. list of library graphs used
        DESCRIPTION.
    updated_ckt_list : TYPE. list of reduced circuit graph
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
    logger.debug(f"Writing results in dir: {result_dir} {updated_ckt_list}")
    input_dir=input_ckt.parents[0]
    VERILOG_FP = open(result_dir / f'{design_name}.v', 'w')
    #printed_mos = []
    #logger.debug("writing spice file for cell generator")

    ## File pointer for spice generator
    #SP_FP = open(result_dir / (design_name + '_blocks.sp'), 'w')
    print_header(VERILOG_FP, design_name)
    design_setup=read_setup(input_dir / (input_ckt.stem + '.setup'))
    try:
        POWER_PINS = [design_setup['GND'][0],design_setup['POWER'][0]]
    except (IndexError, ValueError):
        POWER_PINS=[]
        logger.error("no power and gnd defination, correct setup file")

    #read lef to not write those modules as macros
    lef_path = pathlib.Path(__file__).resolve().parent.parent / 'config'
    all_lef = read_lef(lef_path)
    logger.debug(f"Available library cells: {', '.join(all_lef)}")
    # local hack for deisgn vco_dtype,
    #there requirement is different size for nmos and pmos
    generated_module=[]
    primitives = {}
    duplicate_modules =[]
    for member in updated_ckt_list:
        name = member["name"]
        if name in duplicate_modules:
            continue
        else:
            duplicate_modules.append(name)
        logger.debug(f"Found module: {name} {member['graph'].nodes()}")

        graph = member["graph"]
        logger.debug(f"Reading nodes from graph: {name}")
        for node, attr in graph.nodes(data=True):
            #lef_name = '_'.join(attr['inst_type'].split('_')[0:-1])
            if 'net' in attr['inst_type']: continue
            #Dropping floating ports

            lef_name = attr['inst_type']

            if "values" in attr and (lef_name in all_lef):
                block_name, block_args = generate_lef(
                    lef_name, attr,
                    primitives, design_config, uniform_height)
                #block_name_ext = block_name.replace(lef_name,'')
                logger.debug(f"Created new lef for: {block_name} {lef_name}")
                #Multiple instances of same module
                if 'inst_copy' in attr:
                    for member in updated_ckt_list:
                        if member["name"] == lef_name + attr['inst_copy']:
                            member["name"] = block_name
                    graph.nodes[node]["inst_type"]=block_name
                    all_lef.append(block_name)

                # Only unit caps are generated
                if  block_name.lower().startswith('cap'):
                    graph.nodes[node]['inst_type'] = block_args['primitive']
                    block_args['primitive'] = block_name
                else:
                    graph.nodes[node]['inst_type'] = block_name

                if block_name in primitives:
                    if block_args != primitives[block_name]:
                        logging.warning(f"two different primitve {block_name} of size {primitives[block_name]} {block_args}got approximated to same unit size")
                else:
                    primitives[block_name] = block_args
            elif "values" in attr and 'inst_copy' in attr:
                member["graph"].nodes[node]["inst_type"]= lef_name + attr["inst_copy"]
                all_lef.append(block_name)

            else:
                logger.debug(f"No physical information found for: {name}")
        logger.debug(f"generated data for {name} : {pprint.pformat(primitives, indent=4)}")

    duplicate_modules =[]
    for member in updated_ckt_list:
        name = member["name"]
        graph = member["graph"]
        if not 'const' in member:
            member["const"]=None
        const = member["const"]
        if name in duplicate_modules:
            continue
        else:
            duplicate_modules.append(name)
        logger.debug(f"Found module: {name} {graph.nodes()}")
        inoutpin = []
        floating_ports=[]
        if "ports_match" in member and member["ports_match"]:
            for key in member["ports_match"].keys():
                if key not in POWER_PINS:
                    inoutpin.append(key)
            if member["ports"]:
                logger.debug(f'Found module ports: {member["ports"]} {member.keys()}')
                floating_ports = set(inoutpin) - set(member["ports"]) - set(design_setup['POWER']) -set(design_setup['GND'])

                if len(list(floating_ports))> 0:
                    logger.error(f"floating ports found: {name} {floating_ports}")
                    raise SystemExit('Please remove floating ports')
        else:
            inoutpin = member["ports"]
        if name not in  all_lef:
            logger.debug(f"call verilog writer for block: {name}")
            wv = WriteVerilog(graph, name, inoutpin, updated_ckt_list, POWER_PINS)
            all_array={}
            logger.debug(f"Copy const file for: {name}")
            const_file = CopyConstFile(name, input_dir, result_dir)
            logger.debug(f"cap constraint gen for block: {name}")

            ##Removing constraints to fix cascoded cmc
            if name not in design_setup['DIGITAL'] and name not in lib_names:
                logger.debug(f"call constraint generator writer for block: {name}")
                stop_points=design_setup['POWER']+design_setup['GND']+design_setup['CLOCK']
                if name not in design_setup['NO_CONST']:
                    WriteConst(graph, result_dir, name, inoutpin, member["ports_weight"],all_array, const,stop_points)
                WriteCap(graph, result_dir, name, design_config["unit_size_cap"],all_array)
                check_common_centroid(graph,const_file,inoutpin)
            wv.print_module(VERILOG_FP)
            generated_module.append(name)
    if len(POWER_PINS)>0:
        print_globals(VERILOG_FP,POWER_PINS)

    logger.info("Topology identification done !!!")
    logger.info(f"OUTPUT verilog netlist at: {result_dir}/{design_name}.v")
    logger.info(f"OUTPUT const file at: {result_dir}/{design_name}.const.json")
    return primitives
