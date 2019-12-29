import os
import argparse
import logging
import pathlib

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
elif os.path.exists("./LOG/compiler.log"):
    os.rename("./LOG/compiler.log", "./LOG/compiler.log1")

logging.basicConfig(filename='./LOG/compiler.log', level=logging.DEBUG)
from util import _write_circuit_graph,max_connectivity
from read_netlist import SpiceParser
from match_graph import read_inputs, read_setup,_mapped_graph_list,preprocess_stack,reduce_graph,define_SD,check_nodes,add_parallel_caps,add_series_res
from write_verilog_lef import WriteVerilog, WriteSpice, print_globals,print_header,print_cell_gen_header,generate_lef,WriteConst,FindArray,WriteCap,check_common_centroid
from read_lef import read_lef


def compiler(input_ckt,design_name,flat=0,Debug=False):
    """
    Wrapper file
    """
    input_dir='/'.join(str(input_ckt).split('/')[0:-1])+'/'
    logging.info("Reading subckt %s", input_ckt)
    sp = SpiceParser(input_ckt,design_name,flat)
    circuit = sp.sp_parser()[0]
    logging.info("template parent path: %s",pathlib.Path(__file__).parent)
    lib_path=(pathlib.Path(__file__).parent / '../basic_library/basic_template.sp').resolve()
    logging.info("template library path: %s",lib_path)
    basic_lib = SpiceParser(lib_path)
    library = basic_lib.sp_parser()
    lib_path=(pathlib.Path(__file__).parent / '../basic_library/user_template.sp').resolve()
    user_lib = SpiceParser(lib_path)
    library += user_lib.sp_parser()
    library=sorted(library, key=lambda k: max_connectivity(k["graph"]), reverse=True)
    if Debug==True:
        _write_circuit_graph(circuit["name"], circuit["graph"],
                                     "./circuit_graphs/")
        for lib_circuit in library:
            _write_circuit_graph(lib_circuit["name"], lib_circuit["graph"],
                                         "./circuit_graphs/")
    hier_graph_dict=read_inputs(circuit["name"],circuit["graph"])
    design_setup=read_setup(input_dir+design_name+'.setup')

    UPDATED_CIRCUIT_LIST = []
    for circuit_name, circuit in hier_graph_dict.items():
        logging.info("START MATCHING in circuit: %s", circuit_name)
        G1 = circuit["graph"]
        if circuit_name in design_setup['DIGITAL']:
            mapped_graph_list = _mapped_graph_list(G1, library, design_setup['CLOCK'], True )
        else:
            define_SD(G1,design_setup['POWER'],design_setup['GND'], design_setup['CLOCK'])
            logging.info("no of nodes: %i", len(G1))
            add_parallel_caps(G1)
            add_series_res(G1)
            preprocess_stack(G1)
            initial_size=len(G1)
            delta =1
            while delta > 0:
                logging.info("CHECKING stacked transistors")
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
    return UPDATED_CIRCUIT_LIST
 
def compiler_output(input_ckt,updated_ckt,design_name,unit_size_mos=12,unit_size_cap=12,flat=0,result_dir='./Results/'):
    if not os.path.exists(result_dir):
        os.mkdir(result_dir)
    logging.info("Writing results in dir: %s",result_dir)
    input_dir='/'.join(str(input_ckt).split('/')[0:-1])+'/'
    VERILOG_FP = open(result_dir +  design_name+ '.v', 'w')
    ## File pointer for running cell generator
    LEF_FP = open(result_dir + design_name + '_lef.sh', 'w')
    LEF_FP.write('# ALIGN generated shell file to generate lef')

    logging.info("writing spice file for cell generator")

    ## File pointer for spice generator
    SP_FP = open(result_dir + design_name + '_blocks.sp', 'w')
    print_cell_gen_header(LEF_FP)
    print_header(VERILOG_FP, design_name)
    design_setup=read_setup(input_dir+design_name+'.setup')
    POWER_PINS = [design_setup['POWER'][0],design_setup['GND'][0]]
    #read lef to not write those modules as macros
    lef_path=(pathlib.Path(__file__).parent / '../LEF').resolve()
    ALL_LEF = read_lef(lef_path)
    logging.info("Available library cells: %s", ", ".join(ALL_LEF))
    # local hack for deisgn vco_dtype, 
    #there requirement is different size for nmos and pmos
    if 'vco_dtype_12' in  design_name:
        unit_size_mos=37
    generated_module=[]
    for members in updated_ckt:
        #print(members)
        name = members["name"]
        logging.info("Found module: %s", name )
        inoutpin = []
        logging.info("found ports match: %s",members["ports_match"])
        floating_ports=[]
        if members["ports_match"]:
            for key in members["ports_match"].keys():
                if key not in POWER_PINS:
                    inoutpin.append(key)
            if members["ports"]:
                logging.info("Found module ports kk:%s",members["ports"] )
                floating_ports = list(set(inoutpin) - set(members["ports"]))
                logging.warning("floating port found: %s",floating_ports)
        else:
            inoutpin = members["ports"]


        graph = members["graph"].copy()
        logging.info("Reading nodes from graph: %s", str(graph))
        for node, attr in graph.nodes(data=True):
            #lef_name = '_'.join(attr['inst_type'].split('_')[0:-1])
            if 'net' in attr['inst_type']: continue
            #Dropping floating ports
            #if attr['ports'
            lef_name = attr['inst_type']
            if "values" in attr and (lef_name in ALL_LEF):
                block_name = generate_lef(LEF_FP, lef_name, attr["values"],
                                         ALL_LEF, unit_size_mos, unit_size_cap)
                block_name_ext = block_name.replace(lef_name,'')
                logging.info("Created new lef for: %s", block_name)

                ALL_LEF.append(block_name)
                graph.nodes[node]['inst_type'] = block_name
            else:
                logging.warning("No physical information found for: %s", name)

        if name in ALL_LEF or name in generated_module[:-1]:
            logging.info("writing spice for block: %s", name)
            ws = WriteSpice(graph, name+block_name_ext, inoutpin, updated_ckt)
            ws.print_subckt(SP_FP)
            continue

        #print("inout pins:",inoutpin)
        if name not in  generated_module:
            logging.info("call verilog writer for block: %s", name)
            wv = WriteVerilog(graph, name, inoutpin, updated_ckt, POWER_PINS)
            logging.info("call array finder for block: %s", name)
            all_array=FindArray(graph, input_dir, name )
            logging.info("cap constraint gen for block: %s", name)
            WriteCap(graph, input_dir, name, unit_size_cap,all_array)
            check_common_centroid(graph,input_dir,name,inoutpin)
            if name not in design_setup['DIGITAL']:
                logging.info("call constraint generator writer for block: %s", name)
                #WriteConst(graph, input_dir, name, inoutpin)
            wv.print_module(VERILOG_FP)
            generated_module.append(name)

    print_globals(VERILOG_FP,POWER_PINS)
    LEF_FP.close()
    SP_FP.close()

    print("OUTPUT LEF generator:", result_dir + design_name + "_lef.sh")
    print("OUTPUT verilog netlist at:", result_dir + design_name + ".v")
    print("OUTPUT spice netlist at:", result_dir + design_name + "_blocks.sp")
if __name__ == '__main__':
# %%
    PARSER = argparse.ArgumentParser(
        description="directory path for input circuits")
    PARSER.add_argument("-d",
                        "--dir",
                        type=str,
                        default='../training_set_netlist',
                        help='relative directory path')
    PARSER.add_argument("-f",
                        "--file",
                        type=str,
                        default=None,
                        help='Name of file in the directory. \
                If not provided it reads all files in given dir.')
    PARSER.add_argument("-s",
                        "--subckt",
                        type=str,
                        default=None,
                        help='Top subckt defination in file.\
                        \nIf no name given it takes file name as subckt name. \
                        \nIf there are instances at top level,\
                        a new subckt is created of name filename')
    PARSER.add_argument(
                        "-flat",
                        "--flat",
                        type=int,
                        default=0,
                        help='1 = flatten the netlist, 0= read as hierahical netlist')
    PARSER.add_argument("-U_mos",
                        "--unit_size_mos",
                        type=int,
                        default=10,
                        help='no of fins in unit size')
    PARSER.add_argument("-U_cap",
                        "--unit_size_cap",
                        type=int,
                        default=10,
                        help='no of fins in unit size')
    ARGS = PARSER.parse_args()
    NETLIST_DIR = ARGS.dir
# %%
    if not os.path.isdir(NETLIST_DIR):
        logging.info("Input dir doesn't exist. Please enter a valid dir path")
        print("Input dir doesn't exist. Please enter a valid dir path")

    NETLIST_FILES = os.listdir(NETLIST_DIR)
    if not NETLIST_FILES:
        print("No spice files found in input_circuit directory. exiting")
        logging.info(
            "No spice files found in input_circuit directory. exiting")
        exit(0)
    elif ARGS.file:
        logging.info("Input file: %s", ARGS.file)
        NETLIST_FILES = [ARGS.file]
    for netlist in NETLIST_FILES:
        print("Reading netlist file:", netlist)
        #name = "switched_cap_filter"
        if netlist.endswith('sp') or netlist.endswith('cdl') or ARGS.file:
            logging.info("READING files in dir: %s", NETLIST_DIR)
            logging.info("READ file: %s/%s flat=%i", NETLIST_DIR, netlist,
                         ARGS.flat)
            updated_ckt = compiler(NETLIST_DIR + '/' + netlist, ARGS.subckt,ARGS.flat )
            compiler_output(NETLIST_DIR + '/' + netlist,updated_ckt, ARGS.subckt,ARGS.unit_size_mos , ARGS.unit_size_cap )
        else:
            print("Not a valid file type (.sp).Skipping this file")



