# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
import pickle
import os
import sys
import json
from math import sqrt, ceil

from .util import convert_to_unit, logging
from .merge_nodes import merge_nodes

from collections import Counter

class WriteVerilog:
    """ write hierarchical verilog file """

    def __init__(self, circuit_graph, circuit_name, inout_pin_names,subckt_list, power_pins):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = [] 
        for port in inout_pin_names:
            if port not in power_pins:
                self.pins.append(port)
        self.power_pins=power_pins
        self.subckt_list = subckt_list

    def check_ports_match(self,port,subckt):
        for members in self.subckt_list:
            if members["name"]==subckt and port in members["ports"]:
                return 1
            else:
                logging.warning("no ports match: %s %s",subckt,port)
                return 1

    def print_module(self, fp):
        logging.info("Writing module : %s", self.circuit_name)
        fp.write("\nmodule " + self.circuit_name + " ( ")
        fp.write(', '.join(self.pins))
        fp.write(" ); ")

        if self.inout_pins:
            logging.info("Writing ports : %s", ', '.join(self.inout_pins))
            fp.write("\ninput ")
            fp.write(', '.join(self.pins))
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
                    logging.error("No connectivity info found : %s",
                                 ', '.join(attr["ports"]))
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                mapped_pins = self.map_pins(ports, nets)
                if mapped_pins:
                    fp.write(', '.join(mapped_pins))
                    fp.write(' ); ')
                else:
                    fp.write(' ); ')
                    print("MAPPING NOT CORRECT")

        fp.write("\n\nendmodule\n")

    def map_pins(self, a, b):
        if len(a) == len(b):
            mapped_pins = []
            for ai, bi in zip(a, b):
                if ai not in self.power_pins:
                    mapped_pins.append("." + ai + "(" + bi + ")")

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
                    if a[i] in self.power_pins:
                        mapped_pins= mapped_pins[:-1]

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
            else:
                logging.warning("no ports match: %s %s",subckt,port)

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
                        nets[1:1]=[nets[1]]
                    # add body ports to transistor
                    #if 'PMOS' in attr['inst_type']:
                    #    nets.append('vdd')
                    #elif 'NMOS' in attr['inst_type']:
                    #    nets.append('vss')

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
    #fp.write("\n\n// End HDL models")
    #fp.write("\n// Global nets module")
    fp.write("\n`celldefine")
    fp.write("\nmodule global_power;")
    for i in range(len(power)):
        fp.write("\nsupply" + str(i) + " " + power[i] + ";")

    fp.write("\nendmodule")
    fp.write("\n`endcelldefine\n")
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
        if block_name in available_block_lef:
            return block_name, available_block_lef[block_name]
        logging.info('Generating lef for: %s %s', name, size)
        return block_name, {
            'primitive': name,
            'value': unit_size_cap
        }

        fp.write("\n$PC fabric_" + name + ".py " +
                    " -b " + unit_block_name + 
                    " -n " + str(unit_size_cap))

    # elif name.lower().startswith('res_array_8'):
    #     if 'res' in values.keys():
    #         size = '%g'%(round(values["res"],2))
    #     elif 'r' in values.keys():
    #         size = '%g'%(round(values["r"],2))
    #     else :
    #         convert_to_unit(values)
    #         size = '_'.join(param+str(values[param]) for param in values)
    #     try:
    #         #size = float(size)
    #         res_unit_size = 30 * unit_size_cap
    #         height = ceil(sqrt(float(size) / res_unit_size))
    #         block_name = name + '_' + size.replace('.','p')
    #         if block_name in available_block_lef:
    #             return block_name, available_block_lef[block_name]
    #         logging.info('Generating lef for: %s %s', block_name, size)
    #         fp.write("\n$PC fabric_Res_array.py " +
    #                  " -b " + block_name +
    #                  " -n " + str(height) +
    #                  " -X " + "8" +
    #                  " -r " + size)
    #     except:
    #         block_name = name + '_' + size
                
    # elif name.lower().startswith('res'):
    #     if 'res' in values.keys():
    #         size = '%g'%(round(values["res"],2))
    #     elif 'r' in values.keys():
    #         size = '%g'%(round(values["r"],2))
    #     else :
    #         convert_to_unit(values)
    #         size = '_'.join(param+str(values[param]) for param in values)
    #     block_name = name + '_' + size.replace('.','p')
    #     res_unit_size = 300 
    #     try:
    #         #size = float(size)
    #         height = ceil(sqrt(float(size) / res_unit_size))
    #         if block_name in available_block_lef:
    #             return block_name, available_block_lef[block_name]
    #         logging.info('Generating lef for: %s %s', block_name, size)
    #         fp.write("\n$PC fabric_" + name + ".py " +
    #                  " -b " + block_name +
    #                  " -n " + str(height) +
    #                  " -r " + size)
    #     except:
    #         fp.write("\n$PC fabric_" + name + ".py " +
    #                  " -b " + block_name +
    #                  " -n " + '1'  +
    #                  " -r " + str(res_unit_size))

    # elif name.lower().startswith('inductor') or \
    #     name.lower().startswith('spiral'):
    #     try:
    #         size = round(values["ind"]*1E12,2)
    #     except :
    #         convert_to_unit(values)
    #         size = '_'.join(param+str(values[param]) for param in values)

    #     ind_unit_size = unit_size_cap
    #     height = ceil(sqrt(size / ind_unit_size))
    #     block_name = name + '_' + str(size)
    #     if block_name in available_block_lef:
    #         return block_name, available_block_lef[block_name]
    #     logging.info('Generating lef for: %s %s', block_name, size)
    #     fp.write("\n$PC fabric_" + name + ".py " +
    #              " -b " + block_name +
    #              " -n " + str(height) + ## THIS IS -u (height)
    #              " -r " + str(size))

    else:
        if "nfin" in values.keys():
            size = int(values["nfin"])
            if 'nf' in values.keys():
                size=size*int(values["nf"])
            ## Hack For VCO circuit
            if 'nmos' in name.lower() and unit_size_mos==37:
                unit_size_mos=8
            elif unit_size_mos==37:
                unit_size_mos=10
            no_units = ceil(size / unit_size_mos)

        elif "l" in values.keys():
            size = int(values["l"]*1E+9)
            no_units = ceil(size / unit_size_mos)

        elif "lr" in values.keys():
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)

        logging.info('Generating lef for: %s %s', name, str(size))
        if isinstance(size, int):
            no_units = 2*ceil(size / unit_size_mos)
            square_x = ceil(sqrt(no_units))
            while no_units % square_x != 0:
                square_x += 1
            xval = square_x
            yval = int(no_units / square_x)
            block_name = f"{name}_n{unit_size_mos}_X{xval}_Y{yval}"
            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            logging.info("Generating parametric lef of: %s", block_name)
            return block_name, {
                'primitive': name,
                'value': unit_size_mos,
                'x_cells': xval,
                'y_cells': yval,
                'parameters': values
            }
        else:
            logging.info("No proper parameters found for cell generation")
            block_name = name+"_"+size

    raise NotImplementedError(f"Could not generate LEF for {name}")

def compare_nodes(G,match_pair,traverced,nodes1,nodes2):
    #logging.info("comparing %s,%s, traversed %s %s",nodes1,nodes2,traverced,list(G.neighbors(nodes1)))
    #logging.info("Comparing node: %s %s , traversed:%s",nodes1,nodes2,traverced)
    #match_pair={}
    #logging.info("comparing %s, %s ",G.nodes[nodes1],G.nodes[nodes2])
    if 'net' in G.nodes[nodes1]['inst_type'] and \
        G.nodes[nodes1]['net_type'] == 'external':
            port=True
    else:
        port = False
    if (not port and len(list(G.neighbors(nodes1))) <=2 and \
        set(G.neighbors(nodes1)) == set(G.neighbors(nodes2)) ) or\
        (port and len(list(G.neighbors(nodes1))) ==1):
        for node1 in list(G.neighbors(nodes1)):
            if node1 not in traverced:
                logging.info(node1)
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
    if G.nodes[node1]["inst_type"]=="net" and \
            G.nodes[node2]["inst_type"]=="net" and \
            len(list(G.neighbors(node1)))==len(list(G.neighbors(node2))) and \
            G.nodes[node1]["net_type"] == G.nodes[node2]["net_type"]:
        #logging.info("comparing_nodes, %s %s True",node1,node2)
        return True
    elif (G.nodes[node1]["inst_type"]==G.nodes[node2]["inst_type"] and
        'values' in G.nodes[node1].keys() and 
         G.nodes[node1]["values"]==G.nodes[node2]["values"] and
        len(list(G.neighbors(node1)))==len(list(G.neighbors(node2)))):
        #logging.info("comparing_nodes, %s %s True",node1,node2)
        return True
    else:
        logging.info("comparing_nodes, %s %s False",node1,node2)
        return False
def connection(graph,net):
    conn =[]
    for nbr in list(graph.neighbors(net)):
        #print(graph.nodes[nbr]["ports_match"].items())
        if "ports_match" in graph.nodes[nbr]:
            idx=list(graph.nodes[nbr]["ports_match"].values()).index(net)
            conn.append(nbr+'/'+list(graph.nodes[nbr]["ports_match"].keys())[idx])
    if graph.nodes[net]["net_type"]=="external":
        conn.append(net)
    return conn

def check_common_centroid(graph,const_path,ports):
    """ Reads available const in input dir
        Fix cc cap in const and netlist
    """
    cc_pair={}
    new_const_path = const_path.parents[0] / (const_path.stem + '.const_temp')
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

def WriteCap(graph,input_dir,name,unit_size_cap,all_array):
    const_path = input_dir / (name + '.const')
    new_const_path = input_dir / (name + '.const_temp')
    logging.info(f"writing cap constraints: {const_path}")
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
    logging.info("writing common centroid caps: %s",all_array)
    for _,array in all_array.items():
        n_cap=[]
        cc_caps=[]
        logging.info("group1: %s",array)
        for _,arr in array.items():
            for ele in arr:
                if graph.nodes[ele]['inst_type'].lower().startswith('cap') and \
                    ele not in available_cap_const:
                    if 'cap' in graph.nodes[ele]['values'].keys():
                        size = graph.nodes[ele]['values']["cap"]*1E15
                    elif 'c' in graph.nodes[ele]['values'].keys():
                        size = graph.nodes[ele]['values']["c"]*1E15
                    else: 
                        size = unit_size_cap
                    n_cap.append( str(ceil(size/unit_size_cap)))
                    cc_caps.append(ele)
        if len(n_cap)>0:
            available_cap_const = available_cap_const+ cc_caps
            unit_block_name = '} , {cap_' + str(unit_size_cap) + 'f} )\n'
            cap_line = "CC ( {"+','.join(cc_caps)+"} , {"+','.join(n_cap)+unit_block_name
            logging.info("Cap constraint"+cap_line)
            new_const_fp.write(cap_line)


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

def matching_groups(G,level1):
    similar_groups=[] 
    logging.info("matching groups for all neighbors: %s", level1)
    for l1_node1 in level1:
        for l1_node2 in level1:
            if l1_node1!= l1_node2 and compare_node(G,l1_node1,l1_node2):
                found_flag=0
                #logging.info("similar_group %s",similar_groups)
                #print(l1_node1,l1_node2)
                for index, sublist in enumerate(similar_groups):
                    if l1_node1 in sublist and l1_node2 in sublist:
                        found_flag=1
                        break
                    if l1_node1 in sublist:
                        similar_groups[index].append(l1_node2)
                        found_flag=1
                        #print("found match")

                        break
                    elif l1_node2 in sublist:
                        similar_groups[index].append(l1_node1)
                        found_flag=1
                        #print("found match")
                        break
                if found_flag==0:
                    similar_groups.append([l1_node1,l1_node2])
    return similar_groups
def trace_template(graph, similar_node_groups,visited,template,array):
    next_match={}
    for source,groups in similar_node_groups.items():
        next_match[source]=[]
        for node in groups:
            #print(node)
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
            #level1=[l1 for l1 in level_1a if l1 not in visited]
            next_match[source] +=level1
            visited +=level1

    if match_branches(graph,next_match):
        for source in array.keys():
            array[source]+=next_match[source]
        template +=next_match[list(next_match.keys())[0]]
        logging.info("found matching level: %s,%s",template,similar_node_groups)
        trace_template(graph, next_match,visited,template,array)


def match_branches(graph,nodes_dict):
    #print("matching branches",nodes_dict)
    #match_pair={}
    nbr_values = {}
    for node, nbrs in nodes_dict.items():
        #super_dict={}
        super_list=[]
        for nbr in nbrs:
            #print("checking nbr",nbr,graph.nodes[nbr])
            if graph.nodes[nbr]['inst_type']== 'net':
                super_list.append('net')
                super_list.append(graph.nodes[nbr]['net_type'])
            else:
                super_list.append(graph.nodes[nbr]['inst_type'])
                for v in graph.nodes[nbr]['values'].values():
                    #super_dict.setdefault(k,[]).append(v)
                    #print("value",k,v)
                    super_list.append(v)
        nbr_values[node]=Counter(super_list)
    _,main=nbr_values.popitem()
    for node, val in nbr_values.items():
        if val == main:
            #print("found values",list(val.elements()))
            continue
        else:
            return False
    return True 

def FindArray(graph,input_dir,name):
    templates = {}
    array_of_node = {}
    visited =[]
    all_array = {}

    for node, attr in graph.nodes(data=True):
        #print("node data",graph.nodes[node])
        if  'net' in attr["inst_type"] and len(list(graph.neighbors(node)))>4:
            level1=[l1 for l1 in graph.neighbors(node) if l1 not in visited]
            array_of_node[node]=matching_groups(graph,level1)
            logging.info("finding array:%s,%s",node,array_of_node[node])
            if len(array_of_node[node]) > 0 and len(array_of_node[node][0])>1:
                similar_node_groups = {}
                for el in array_of_node[node][0]:
                    similar_node_groups[el]=[el]
                templates[node]=[list(similar_node_groups.keys())[0]]
                visited=array_of_node[node][0]+[node]
                array=similar_node_groups
                trace_template(graph,similar_node_groups,visited,templates[node],array)
                logging.info("similar groups final, %s",array)
                all_array[node]=array
    return all_array
                #match_branches(graph,nodes_dict)
def WriteConst(graph, input_dir, name, ports, working_dir):

    # Copy const file to working directory if needed
    input_const_file = (input_dir / (name + '.const'))
    const_file = (working_dir / (name + '.const'))
    if input_const_file.exists() and input_const_file.is_file():
        if const_file == input_const_file:
            (input_dir / (name + '.const.old')).write_text(input_const_file.read_text())
        else:
            const_file.write_text(input_const_file.read_text())

    check_common_centroid(graph,const_file,ports)
    logging.info("writing constraints: %s",const_file)
    #const_fp.write(str(ports))
    #const_fp.write(str(graph.nodes()))
    traverced =[]
    all_match_pairs={}
    for port in ports:
        if port in graph.nodes():
            #while len(list(graph.neighbors(port)-set(traverced)))==1:
            #nbr = list(graph.neighbors(port))
            pair ={}
            traverced.append(port)
            compare_nodes(graph, pair, traverced, port, port)
            if pair:
                #const_fp.write(port)
                all_match_pairs.update(pair)
    existing_SymmBlock =False

    # Read contents
    if const_file.exists() and const_file.is_file():
        with open(const_file) as f:
            content = f.readlines()
            if 'SymmBlock' in content:
                existing_SymmBlock = True
            elif 'SymmNet' in content:
                existing_SymmNet += content.strip()

    const_fp = open(const_file, 'a+')
    if len(list(all_match_pairs.keys()))>0:
        symmBlock = "SymmBlock ("
        for key, value in all_match_pairs.items():
            if graph.nodes[key]["inst_type"]!="net":
                if key ==value:
                    symmBlock = symmBlock+' {'+key+ '} ,'
                else:
                    symmBlock = symmBlock+' {'+key+ ','+value+'} ,'
            else: 
                if len(list(graph.neighbors(key)))<3:
                    symmNet = "SymmNet ( {"+key+','+','.join(connection(graph,key)) + \
                            '} , {'+value+','+','.join(connection(graph,value)) +'} )\n'
                    const_fp.write(symmNet)


        symmBlock = symmBlock[:-1]+')\n'
        if not existing_SymmBlock:
            const_fp.write(symmBlock)
        const_fp.close()
