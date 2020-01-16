import pathlib
import pprint

from .util import _write_circuit_graph, max_connectivity
from .read_netlist import SpiceParser
from .match_graph import read_inputs, read_setup,_mapped_graph_list,preprocess_stack,reduce_graph,define_SD,check_nodes,add_parallel_caps,add_series_res
from .write_verilog_lef import WriteVerilog, WriteSpice, print_globals,print_header,generate_lef
from .write_verilog_lef import WriteConst, FindArray, WriteCap, check_common_centroid, CopyConstFile
from .read_lef import read_lef

import logging
logger = logging.getLogger(__name__)

def generate_hierarchy(netlist, subckt, output_dir, flatten_heirarchy, unit_size_mos , unit_size_cap):
    updated_ckt,library = compiler(netlist, subckt, flatten_heirarchy)
    return compiler_output(netlist, library, updated_ckt, subckt, output_dir, unit_size_mos , unit_size_cap)

def compiler(input_ckt:pathlib.Path, design_name:str, flat=0,Debug=False):
    logger.info("Starting topology identification...")
    input_dir=input_ckt.parents[0]
    logger.debug(f"Reading subckt {input_ckt}")
    sp = SpiceParser(input_ckt, design_name, flat)
    circuit = sp.sp_parser()[0]

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
    logger.info(f"dont use cells: {design_setup['DONT_USE_CELLS']}")
    if len(design_setup['DONT_USE_CELLS'])>0:
        library=[lib_ele for lib_ele in library if lib_ele['name'] not in design_setup['DONT_USE_CELLS']]

    if Debug==True:
        _write_circuit_graph(circuit["name"], circuit["graph"],
                                     "./circuit_graphs/")
        for lib_circuit in library:
            _write_circuit_graph(lib_circuit["name"], lib_circuit["graph"],
                                         "./circuit_graphs/")
    hier_graph_dict=read_inputs(circuit["name"],circuit["graph"])

    UPDATED_CIRCUIT_LIST = []
    for circuit_name, circuit in hier_graph_dict.items():
        logger.debug(f"START MATCHING in circuit: {circuit_name}")
        G1 = circuit["graph"]
        if circuit_name in design_setup['DIGITAL']:
            mapped_graph_list = _mapped_graph_list(G1, library, design_setup['CLOCK'], True )
        else:
            define_SD(G1,design_setup['POWER'],design_setup['GND'], design_setup['CLOCK'])
            logger.debug(f"no of nodes: {len(G1)}")
            add_parallel_caps(G1)
            add_series_res(G1)
            preprocess_stack(G1)
            initial_size=len(G1)
            delta =1
            while delta > 0:
                logger.debug("CHECKING stacked transistors")
                preprocess_stack(G1)
                delta = initial_size - len(G1)
                initial_size = len(G1)
            mapped_graph_list = _mapped_graph_list(G1, library, design_setup['CLOCK'], False )
        updated_circuit, Grest = reduce_graph(G1, mapped_graph_list, library)
        check_nodes(updated_circuit)
        UPDATED_CIRCUIT_LIST.extend(updated_circuit)

        UPDATED_CIRCUIT_LIST.append({
            "name": circuit_name,
            "graph": Grest,
            "ports":circuit["ports"],
            "ports_match": circuit["connection"],
            "size": len(Grest.nodes())
        })
    return UPDATED_CIRCUIT_LIST, library

def compiler_output(input_ckt, library, updated_ckt, design_name, result_dir, unit_size_mos=12, unit_size_cap=12):
    if not result_dir.exists():
        result_dir.mkdir()
    logger.debug(f"Writing results in dir: {result_dir}")
    input_dir=input_ckt.parents[0]
    VERILOG_FP = open(result_dir / f'{design_name}.v', 'w')

    logger.debug("writing spice file for cell generator")

    ## File pointer for spice generator
    SP_FP = open(result_dir / (design_name + '_blocks.sp'), 'w')
    print_header(VERILOG_FP, design_name)
    design_setup=read_setup(input_dir / (input_ckt.stem + '.setup'))
    try:
        POWER_PINS = [design_setup['POWER'][0],design_setup['GND'][0]]
    except (IndexError, ValueError):
        POWER_PINS=[]
        logger.error("no power and gnd defination, correct setup file")

    #read lef to not write those modules as macros
    lef_path = pathlib.Path(__file__).resolve().parent.parent / 'config'
    ALL_LEF = read_lef(lef_path)
    logger.debug(f"Available library cells: {', '.join(ALL_LEF)}")
    # local hack for deisgn vco_dtype,
    #there requirement is different size for nmos and pmos
    if 'vco_dtype_12' in  design_name:
        unit_size_mos=37
    generated_module=[]
    primitives = {}
    duplicate_modules =[]
    for members in updated_ckt:
        #print(members)
        name = members["name"]
        if name in duplicate_modules:
            continue
        else:
            duplicate_modules.append(name)
        logger.debug(f"Found module: {name}")
        inoutpin = []
        logger.debug(f'found ports match: {members["ports_match"]}')
        floating_ports=[]
        if members["ports_match"]:
            for key in members["ports_match"].keys():
                if key not in POWER_PINS:
                    inoutpin.append(key)
            if members["ports"]:
                logger.debug(f'Found module ports kk: {members["ports"]}')
                floating_ports = list(set(inoutpin) - set(members["ports"]))
                if len(floating_ports)> 0:
                    logger.error(f"floating ports found: {name} {floating_ports}")
                    raise SystemExit('Please remove floating ports')
        else:
            inoutpin = members["ports"]

        graph = members["graph"].copy()
        logger.debug(f"Reading nodes from graph: {graph}")
        for node, attr in graph.nodes(data=True):
            #lef_name = '_'.join(attr['inst_type'].split('_')[0:-1])
            if 'net' in attr['inst_type']: continue
            #Dropping floating ports
            #if attr['ports'
            lef_name = attr['inst_type']
            if "values" in attr and (lef_name in ALL_LEF):
                block_name, block_args = generate_lef(
                    lef_name, attr["values"],
                    primitives, unit_size_mos, unit_size_cap)
                block_name_ext = block_name.replace(lef_name,'')
                logger.debug(f"Created new lef for: {block_name}")
                # Only unit caps are generated
                if  block_name.lower().startswith('cap'):
                    graph.nodes[node]['inst_type'] = block_args['primitive']
                    block_args['primitive']=block_name
                else:
                    graph.nodes[node]['inst_type'] = block_name

                if block_name in primitives:
                    assert block_args == primitives[block_name]
                else:
                    primitives[block_name] = block_args
            else:
                logger.info(f"No physical information found for: {name}")

        if name in ALL_LEF:
            logger.debug(f"writing spice for block: {name}")
            ws = WriteSpice(graph, name+block_name_ext, inoutpin, updated_ckt)
            ws.print_subckt(SP_FP)
            continue

        logger.debug(f"generated data for {name} : {pprint.pformat(primitives, indent=4)}")
        if name not in  ALL_LEF:
            logger.debug(f"call verilog writer for block: {name}")
            wv = WriteVerilog(graph, name, inoutpin, updated_ckt, POWER_PINS)
            logger.debug(f"call array finder for block: {name}")
            all_array=FindArray(graph, input_dir, name )
            logger.debug(f"Copy const file for: {name}")
            const_file = CopyConstFile(name, input_dir, result_dir)
            logger.debug(f"cap constraint gen for block: {name}")
            WriteCap(graph, result_dir, name, unit_size_cap,all_array)
            check_common_centroid(graph,const_file,inoutpin)
            ##Removinf constraints to fix cascoded cmc
            lib_names=[lib_ele['name'] for lib_ele in library]
            if name not in design_setup['DIGITAL'] and name not in lib_names:
                logger.debug(f"call constraint generator writer for block: {name}")
                stop_points=design_setup['DIGITAL']+design_setup['CLOCK']
                WriteConst(graph, result_dir, name, inoutpin, stop_points)
            wv.print_module(VERILOG_FP)
            generated_module.append(name)
    if len(POWER_PINS)>0:
        print_globals(VERILOG_FP,POWER_PINS)
    SP_FP.close()

    logger.info("Topology identification done !!!")
    logger.info(f"OUTPUT verilog netlist at: {result_dir}/{design_name}.v")
    logger.info(f"OUTPUT spice netlist at: {result_dir}/{design_name}_blocks.sp")
    logger.info(f"OUTPUT const file at: {result_dir}/{design_name}.const")

    return primitives
