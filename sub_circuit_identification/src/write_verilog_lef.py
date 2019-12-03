# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
import pickle
import os
import logging
import argparse
import sys
import json
from math import sqrt, ceil
from read_lef import read_lef
from util import convert_to_unit
from merge_nodes import merge_nodes

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
elif os.path.exists("./LOG/writer.log"):
    os.rename("./LOG/writer.log", "./LOG/writer.log1")    
logging.basicConfig(filename='./LOG/writer.log', level=logging.DEBUG)



class WriteVerilog:
    """ write hierarchical verilog file """

    def __init__(self, circuit_graph, circuit_name, inout_pin_names,subckt_list):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = inout_pin_names
        self.subckt_list = subckt_list

    def check_ports_match(self,port,subckt):
        for members in self.subckt_list:
            if members["name"]==subckt and port in members["ports"]:
                return 1

    def print_module(self, fp):
        logging.info("Writing module : %s", self.circuit_name)
        fp.write("\nmodule " + self.circuit_name + " ( ")
        fp.write(', '.join(self.pins))
        fp.write(" ); ")

        if self.inout_pins:
            logging.info("Writing ports : %s", ', '.join(self.inout_pins))
            fp.write("\ninput ")
            fp.write(', '.join(self.inout_pins))
            fp.write(";\n")

        for node, attr in self.circuit_graph.nodes(data=True):
            if 'source' in attr['inst_type']:
                logging.info("Skipping source nodes : %s", node)
                continue
            if 'net' not in attr['inst_type']:
                logging.info("Writing node: %s", node)
                fp.write("\n" + attr['inst_type'] + " " + node + ' ( ')
                ports = []
                nets = []
                if "ports_match" in attr:
                    logging.info("Nets connected to ports: %s",attr["ports_match"])
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
                elif "connection" in attr:
                    try:
                        logging.info("connection to ports: %s",attr["connection"])
                        for key, value in attr["connection"].items():
                            if self.check_ports_match(key,attr['inst_type']):
                                ports.append(key)
                                nets.append(value)                    
                    except:
                        logging.error("ERROR: Subckt %s defination not found",attr['inst_type'])

                else:
                    logging.info("No connectivity info found : %s",
                                 ', '.join(attr["ports"]))
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                mapped_pins = self.map_pins(ports, nets)
                if mapped_pins:
                    fp.write(', '.join(mapped_pins))
                    fp.write(' ); ')
                else:
                    print("MAPPING NOT CORRECT")

        fp.write("\n\nendmodule\n")

    def map_pins(self, a, b):
        if len(a) == len(b):
            mapped_pins = []
            for i in range(len(a)):
                mapped_pins.append("." + a[i] + "(" + b[i] + ")")

            return mapped_pins
        elif len(set(a)) == len(set(b)):
            if len(a) > len(b):
                mapped_pins = []
                check_sort = []
                no_of_sort = 0
                for i in range(len(a)):
                    if a[i] in check_sort:
                        mapped_pins.append(mapped_pins[check_sort.index(a[i])])
                        no_of_sort += 1
                    else:
                        mapped_pins.append("." + a[i] + "(" +
                                           b[i - no_of_sort] + ")")
                        check_sort.append(a[i])

                return mapped_pins

        else:
            print("unmatched ports found")
            return 0

class WriteSpice:
    """ write hierarchical verilog file """

    def __init__(self, circuit_graph, circuit_name, inout_pin_names,subckt_list):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = inout_pin_names
        self.subckt_list = subckt_list

    def check_ports_match(self,port,subckt):
        for members in self.subckt_list:
            if members["name"]==subckt and port in members["ports"]:
                return 1

    def print_subckt(self, fp):
        logging.info("Writing module : %s", self.circuit_name)
        fp.write("\n.subckt " + self.circuit_name + " ")
        fp.write(' '.join(self.pins))

        for node, attr in self.circuit_graph.nodes(data=True):
            if 'source' in attr['inst_type']:
                logging.info("Skipping source nodes : %s", node)
                continue
            if 'net' not in attr['inst_type']:
                logging.info("Writing node: %s", attr['inst_type'])
                fp.write("\n" + node + ' ')
                ports = []
                nets = []
                if "ports_match" in attr:
                    logging.info("Nets connected to ports: %s",attr["ports_match"])
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
                    # transitor with shorted terminals
                    if 'DCL_NMOS' in attr['inst_type']:
                        nets[1:1]=[nets[0]]
                    elif 'DCL_PMOS' in attr['inst_type']:
                        nets[1:1]=[nets[2]]
                    # add body ports to transistor
                    if 'PMOS' in attr['inst_type']:
                        nets.append('vdd')
                    elif 'NMOS' in attr['inst_type']:
                        nets.append('vss')

                else:
                    logging.error("No connectivity info found : %s",
                                 ', '.join(attr["ports"]))
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                fp.write(' '.join(nets) +' '+ attr['inst_type'] + ' '+ concat_values(attr['values']) )

        fp.write("\n.ends "+self.circuit_name+ "\n")
        
def concat_values(values):
    merged_values =""
    for key,value in values.items():
        merged_values = merged_values+' '+key+'='+str(value).replace('.0','')
    return merged_values


def print_globals(fp, power):
    """ Write global variables"""
    fp.write("\n\n// End HDL models")
    fp.write("\n// Global nets module")
    fp.write("\n`celldefine")
    fp.write("\nmodule cds_globals;\n")
    for i in range(len(power)):
        fp.write("\nsupply" + str(i) + " " + power[i] + ";")

    fp.write("\n\nendmodule")
    fp.write("\n`endcelldefine")
    fp.close()


def print_header(fp, filename):
    """ Write Verilog header"""
    fp.write("//Verilog block level netlist file for " + filename)
    fp.write("\n//Generated by UMN for ALIGN project \n\n")

def print_cell_gen_header(fp):
    fp.write("#!/bin/bash")
    fp.write("\nPC=$1\n")


def generate_lef(fp, name, values, available_block_lef, 
                 unit_size_mos=12 , unit_size_cap=12):
    """ Creates a shell script to generate parameterized lef"""
    logging.info("checking lef for:%s,%s",name,values)
    #for param, value in size.items():

    if name.lower().startswith('cap'):
        #print("all val",values)
        if 'cap' in values.keys():
            size = '%g'%(round(values["cap"]*1E15,4))
        elif 'c' in values.keys():
            size = '%g'%(round(values["c"]*1E15,4))
        else: 
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        logging.info("Found cap with size: %s %d",size,unit_size_cap )                
        block_name = name + '_' + size.replace('.','p').replace('-','_neg_') + 'f'
        unit_block_name = 'cap_' + str(unit_size_cap) + 'f'
        if not block_name in available_block_lef:
            logging.info('Generating lef for: %s %s', name, size)
            fp.write("\n$PC fabric_" + name + ".py " +
                     " -b " + unit_block_name + 
                     " -n " + str(unit_size_cap))
            #fp.write("\n$PC fabric_" + name + ".py " +
            #         " -b " + block_name + 
            #         " -n " + str(size))

    elif name.lower().startswith('res_array_8'):
        if 'res' in values.keys():
            size = '%g'%(round(values["res"],2))
        elif 'r' in values.keys():
            size = '%g'%(round(values["r"],2))
        else :
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        try:
            #size = float(size)
            res_unit_size = 30 * unit_size_cap
            height = ceil(sqrt(float(size) / res_unit_size))
            block_name = name + '_' + size.replace('.','p')
            if block_name in available_block_lef:
                return block_name
            logging.info('Generating lef for: %s %s', block_name, size)
            fp.write("\n$PC fabric_Res_array.py " +
                     " -b " + block_name +
                     " -n " + str(height) +
                     " -X " + "8" +
                     " -r " + size)
        except:
            block_name = name + '_' + size
                
    elif name.lower().startswith('res'):
        if 'res' in values.keys():
            size = '%g'%(round(values["res"],2))
        elif 'r' in values.keys():
            size = '%g'%(round(values["r"],2))
        else :
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        block_name = name + '_' + size.replace('.','p')
        res_unit_size = 300 
        try:
            #size = float(size)
            height = ceil(sqrt(float(size) / res_unit_size))
            if block_name in available_block_lef:
                return block_name
            logging.info('Generating lef for: %s %s', block_name, size)
            fp.write("\n$PC fabric_" + name + ".py " +
                     " -b " + block_name +
                     " -n " + str(height) +
                     " -r " + size)
        except:
            fp.write("\n$PC fabric_" + name + ".py " +
                     " -b " + block_name +
                     " -n " + '1'  +
                     " -r " + str(res_unit_size))

    elif name.lower().startswith('inductor') or \
        name.lower().startswith('spiral'):
        try:
            size = round(values["ind"]*1E12,2)
        except :
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
            
        ind_unit_size = unit_size_cap
        height = ceil(sqrt(size / ind_unit_size))
        block_name = name + '_' + str(size)
        if block_name in available_block_lef:
            return block_name
        logging.info('Generating lef for: %s %s', block_name, size)
        fp.write("\n$PC fabric_" + name + ".py " +
                 " -b " + block_name +
                 " -n " + str(height) +
                 " -r " + str(size))
        
    else:
        #print("other param",values)
        if "nfin" in values.keys():
            size = int(values["nfin"])
            if 'nf' in values.keys():
                size=size*int(values["nf"])
            no_units = ceil(size / unit_size_mos)

        elif "l" in values.keys():
            size = int(values["l"]*1E+9)
            no_units = ceil(size / unit_size_mos)

        elif "lr" in values.keys():
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
            #size = int(values["lr"]*1E+9)
            
        #print(size)
        logging.info('Generating lef for: %s %s', name, str(size))
        if isinstance(size, int):
            no_units = ceil(size / unit_size_mos)
            square_x = ceil(sqrt(no_units))
            while no_units % square_x != 0:
                square_x += 1
            xval = str(square_x)
            yval = str(int(no_units / square_x))
            block_name = (name + "_n" + str(unit_size_mos) +
                        "_X" + xval + "_Y" + yval)
            if block_name in available_block_lef:
                return block_name
            logging.info("Generating parametric lef of: %s", block_name)
            fp.write("\n$PC Align_primitives.py -p " + name +
                     " -b " + block_name +
                     " -n " + str(unit_size_mos) +
                     " -X " + xval +
                     " -Y " + yval +
                     " --params " + "'" + json.dumps(values) + "'")
        else:
            logging.info("No proper marameters found for cell generation")
            block_name = name+"_"+size       

    return block_name

def compare_nodes(G,match_pair,traverced,nodes1,nodes2):
    #print(G.node[node1],G.node[node2])
    #match_pair={}
    if len(list(G.neighbors(nodes1))) <=2 and \
            set(G.neighbors(nodes1)) == set(G.neighbors(nodes2)):
        for node1 in list(G.neighbors(nodes1)):
            if node1 not in traverced:
                #print(nodes1,nodes2,list(G.neighbors(nodes1)),list(G.neighbors(nodes2)))
                match_pair[node1]=node1
                compare_nodes(G,match_pair,traverced,node1,node1)
    for node1 in list(G.neighbors(nodes1)):
        if node1 not in traverced and \
                node1 not in match_pair.keys():
            for node2 in list(G.neighbors(nodes2)):
                if node1 != node2 and node2 not in traverced:
                    if compare_node(G,node1,node2):
                        if G.get_edge_data(nodes1,node1)['weight'] == G.get_edge_data(nodes2,node2)['weight']:
                            #match_pair[nodes1][1].append(node1)
                            #match_pair[nodes2][2].append(node2)
                            match_pair[node1]=node2
                            #print(node1,node2)
                            traverced.append(node1)
                            traverced.append(node2)
                            compare_nodes(G,match_pair,traverced,node1,node2)                    
    return match_pair
def compare_node(G,node1,node2):
    if G.node[node1]["inst_type"]=="net" and \
            G.node[node2]["inst_type"]=="net" and \
            len(list(G.neighbors(node1)))==len(list(G.neighbors(node2))) and \
            G.node[node1]["net_type"] == G.node[node2]["net_type"]:
        return True
    elif (G.node[node1]["inst_type"]==G.node[node2]["inst_type"] and
        'values' in G.node[node1].keys() and 
         G.node[node1]["values"]==G.node[node2]["values"] and
        len(list(G.neighbors(node1)))==len(list(G.neighbors(node2)))):
        return True
    else:
        return False
def connection(G,net):
    conn =[]
    for nbr in list(G.neighbors(net)):
        #print(graph.node[nbr]["ports_match"].items())
        if "ports_match" in graph.node[nbr]:
            idx=list(graph.node[nbr]["ports_match"].values()).index(net)
            conn.append(nbr+'/'+list(graph.node[nbr]["ports_match"].keys())[idx])
    if graph.node[net]["net_type"]=="external":
        conn.append(net)
    return conn

def check_common_centroid(graph,input_dir,name,ports):
    """ Reads available const in input dir
        Fix cc cap in const and netlist
    """
    cc_pair={}
    const_path=input_dir + name + '.const'
    new_const_path = input_dir + name + '.const_temp'
    if os.path.isfile(const_path): 
        print('Reading const file for common centroid', const_path)
        const_fp = open(const_path, "r")
        new_const_fp = open(new_const_path, "w")
        line = const_fp.readline()
        while line:
            if line.startswith("CC") and len(line.strip().split(','))>=5:
                caps_in_line = line[line.find("{")+1:line.find("}")]
                updated_cap = caps_in_line.replace(',','_')
                cap_blocks = caps_in_line.strip().split(',')
                matched_ports ={}
                for idx,cap_block in enumerate(cap_blocks):
                    cc_pair.update({cap_block: updated_cap})
                    conn = list(graph.neighbors(cap_block))
                    matched_ports['MINUS'+str(idx)] = conn[0]
                    matched_ports['PLUS'+str(idx)]= conn[1]
                print("matched_ports",cc_pair,matched_ports)
                line = line.replace(caps_in_line,updated_cap)
                graph, _ = merge_nodes(
                        graph, 'Cap_cc',cap_blocks , matched_ports)
            new_const_fp.write(line)
            line=const_fp.readline()
    
        const_fp.close()
        new_const_fp.close()
        os.rename(new_const_path, const_path)
    else:
        print("Couldn't find constraint file",const_path," (might be okay)")

    return(cc_pair)

def WriteCap(graph,input_dir,name,unit_size_cap):
    const_path = input_dir + name + '.const'
    new_const_path = input_dir + name + '.const_temp'
    logging.info("writing cap constraints:"+input_dir + name + '.const')
    available_cap_const = []
    if os.path.isfile(const_path): 
        print('Reading const file for cap', const_path)
        const_fp = open(const_path, "r")
        new_const_fp = open(new_const_path, "w")
        line = const_fp.readline()
        while line:
            if line.startswith("CC"):
                caps_in_line = line[line.find("{")+1:line.find("}")]
                cap_blocks = caps_in_line.strip().split(',')
                available_cap_const = available_cap_const+cap_blocks
            new_const_fp.write(line)
            logging.info("cap const %s",line)
            line=const_fp.readline()
        const_fp.close()
    else:
        new_const_fp = open(new_const_path, "w")
        logging.info("Creating new const file"+new_const_path)


    for node, attr in graph.nodes(data=True):
        if attr['inst_type'].lower().startswith('cap')  and node not in available_cap_const:
            if 'cap' in attr['values'].keys():
                size = attr['values']["cap"]*1E15
            elif 'c' in attr['values'].keys():
                size = attr['values']["c"]*1E15
            else: 
                size = unit_size_cap
            n_cap = str(ceil(size/unit_size_cap))
            unit_block_name = '} , {cap_' + str(unit_size_cap) + 'f} )\n'
            cap_line = "CC ( {"+node+"} , {"+n_cap+unit_block_name
            logging.info("Cap constraint"+cap_line)
            new_const_fp.write(cap_line)
            available_cap_const.append(node)
    new_const_fp.close()
    if os.stat(new_const_path).st_size ==0:
        os.remove(new_const_path)
    else:
        os.rename(new_const_path, const_path)


def WriteConst(graph,input_dir,name,ports):
    check_common_centroid(graph,input_dir,name,ports)
    const_fp = open(input_dir + name + '.const', 'a+')
    print("writing constraints:",input_dir + name + '.const')
    #const_fp.write(str(ports))
    #const_fp.write(str(graph.nodes()))
    traverced =[]
    all_match_pairs={}
    for port in ports:
        if port in graph.nodes():
            #while len(list(graph.neighbors(port)-set(traverced)))==1:
            nbr = list(graph.neighbors(port))
            pair ={}
            traverced.append(port)
            compare_nodes(graph, pair, traverced, port, port)
            if pair:
                #const_fp.write(port)
                all_match_pairs.update(pair)
    symmBlock = "SymmBlock ("
    for key, value in all_match_pairs.items():
        if graph.node[key]["inst_type"]!="net":
            if key ==value:
                symmBlock = symmBlock+' {'+key+ '} ,'
            else:
                symmBlock = symmBlock+' {'+key+ ','+value+'} ,'
        else:
            if len(list(graph.neighbors(key)))<3:
                symmNet = "SymmNet ( {"+key+','+','.join(connection(graph,key)) + \
                        '} , {'+value+','+','.join(connection(graph,value)) +'} )\n'
                const_fp.write(symmNet)


    symmBlock = symmBlock[:-1]+')'
    const_fp.write(symmBlock)
    const_fp.close()
#%%
if __name__ == '__main__':
    if not os.path.exists("./Results/"):
        os.mkdir("./Results/")
    RESULT_DIR = "./Results/"
    logging.info("Writing results in ./Results dir: ")

    PARSER = argparse.ArgumentParser(
        description="directory path for input circuits")
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

    FILE_NAMES = os.listdir(RESULT_DIR)
    INPUT_PICKLE = []
    for files in FILE_NAMES:
        if files.endswith('.p'):
            INPUT_PICKLE.append(files[:-2])
            logging.info("Searching file: %s", files)
    logging.info("Found files: %s", ", ".join(INPUT_PICKLE))
    try:
        INPUT_PICKLE = INPUT_PICKLE[0]
    except ValueError:
        print("ERROR: No input file. Exiting verilog writer")
        sys.exit()
    logging.info("Picking first file for generating results: %s", INPUT_PICKLE)
    # write a verilog file
    VERILOG_FP = open(RESULT_DIR + INPUT_PICKLE + '.v', 'w')
    LEF_FP = open(RESULT_DIR + INPUT_PICKLE + '_lef.sh', 'w')
    logging.info("writing spice file for cell generator")
    SP_FP = open(RESULT_DIR + INPUT_PICKLE + '_blocks.sp', 'w')
    print_cell_gen_header(LEF_FP)
    LEF_FP.write('# file to generate lef')
    print_header(VERILOG_FP, INPUT_PICKLE)
    POWER_PINS = ["vdd!", "gnd"]
    #read lef to not write those modules as macros
    ALL_LEF = read_lef()
    logging.info("Reading available lef: %s", ", ".join(ALL_LEF))

    UNIT_SIZE_CAP = ARGS.unit_size_cap
    UNIT_SIZE_MOS = ARGS.unit_size_mos
    logging.info("Unit cap cell size: %s", str(UNIT_SIZE_CAP))
    logging.info("Unit mos cell size: %s", str(UNIT_SIZE_MOS))
    logging.info("Reading file: %s", RESULT_DIR + INPUT_PICKLE + '.p')

    with open(RESULT_DIR + INPUT_PICKLE + '.p', 'rb') as fp:
        list_graph = pickle.load(fp)
    #print(list_graph)
    generated_module=[]
    for members in list_graph:
        #print(members)
        name = members["name"]
        logging.info("Found module: %s", name )
        inoutpin = []
        logging.info("found ports match: %s",members["ports_match"])
        floating_ports=[]
        if members["ports_match"]:
            for key, value in members["ports_match"].items():
                inoutpin.append(key)
            if members["ports"]:
                logging.info("Found module ports:%s",members["ports"] )
                floating_ports = list(set(inoutpin) - set(members["ports"]))
        else:
            inoutpin = members["ports"]
        if len(floating_ports)>0:
            logging.warning("Floating ports in design:%s,%s",len(floating_ports),floating_ports)
            inoutpin=members["ports"]
        
        graph = members["lib_graph"].copy()
        logging.info("Reading nodes from graph: %s", str(graph))
        for node, attr in graph.nodes(data=True):
            #lef_name = '_'.join(attr['inst_type'].split('_')[0:-1])
            if 'net' in attr['inst_type']: continue
            #Dropping floating ports
            #if attr['ports'
            lef_name = attr['inst_type']
            if "values" in attr and (lef_name in ALL_LEF):
                block_name = generate_lef(LEF_FP, lef_name, attr["values"],
                                         ALL_LEF, UNIT_SIZE_MOS, UNIT_SIZE_CAP)
                block_name_ext = block_name.replace(lef_name,'')
                logging.info("Created new lef for: %s", block_name)

                ALL_LEF.append(block_name)
                graph.nodes[node]['inst_type'] = block_name
            else:
                logging.warning("No physical information found for: %s",
                             name)

        if name in ALL_LEF or name in generated_module[:-1]:
            logging.info("writing spice for block: %s", name)
            ws = WriteSpice(graph, name+block_name_ext, inoutpin, list_graph)
            ws.print_subckt(SP_FP)
            continue

        #print("inout pins:",inoutpin)
        if name not in  generated_module:
            logging.info("writing verilog for block: %s", name)
            wv = WriteVerilog(graph, name, inoutpin, list_graph)
            #wc = WriteConst(graph, './input_circuit/', name, inoutpin)
            wc = WriteCap(graph, './input_circuit/', name, UNIT_SIZE_CAP)
            wv.print_module(VERILOG_FP)
            generated_module.append(name)


    LEF_FP.close()
    SP_FP.close()

    print("OUTPUT LEF generator:", RESULT_DIR + INPUT_PICKLE + "_lef.sh")
    print("OUTPUT verilog netlist at:", RESULT_DIR + INPUT_PICKLE + ".v")
    print("OUTPUT spice netlist at:", RESULT_DIR + INPUT_PICKLE + "_blocks.sp")
