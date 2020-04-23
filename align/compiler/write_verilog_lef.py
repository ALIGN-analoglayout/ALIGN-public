# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
from math import sqrt, ceil,floor

from .util import convert_to_unit

import logging
logger = logging.getLogger(__name__)



class WriteVerilog:
    """ write hierarchical verilog file """

    def __init__(self, circuit_graph, circuit_name, inout_pin_names,subckt_list, power_pins):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = []
        for port in sorted(inout_pin_names):
            if port not in power_pins:
                self.pins.append(port)
        self.power_pins=power_pins
        self.subckt_list = subckt_list

    def print_module(self, fp):
        logger.debug(f"Writing module : {self.circuit_name}")
        fp.write("\nmodule " + self.circuit_name + " ( ")
        fp.write(', '.join(self.pins))
        fp.write(" ); ")

        if self.inout_pins:
            logger.debug(f"Writing ports : {', '.join(self.inout_pins)}")
            fp.write("\ninput ")
            fp.write(', '.join(self.pins))
            fp.write(";\n")

        for node, attr in self.circuit_graph.nodes(data=True):
            if 'source' in attr['inst_type']:
                logger.debug(f"Skipping source nodes : {node}")
                continue
            if 'net' not in attr['inst_type']:
                logger.debug(f"Writing node: {node} {attr}")
                fp.write("\n" + attr['inst_type'] + " " + node + ' ( ')
                ports = []
                nets = []
                if "ports_match" in attr:
                    logger.debug(f'Nets connected to ports: {attr["ports_match"]}')
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
                elif "connection" in attr:
                    try:
                        logger.debug(f'connection to ports: {attr["connection"]}')
                        for key, value in attr["connection"].items():
                            if check_ports_match(self.subckt_list,key,attr['inst_type']):
                                ports.append(key)
                                nets.append(value)
                    except:
                        logger.error(f"ERROR: Subckt {attr['inst_type']} defination not found")

                else:
                    logger.error(f"No connectivity info found : {', '.join(attr['ports'])}")
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                mapped_pins = self.map_pins(ports, nets)
                if mapped_pins:
                    fp.write(', '.join(mapped_pins))
                    fp.write(' ); ')
                else:
                    fp.write(' ); ')
                    logger.warning(f"Unconnected module, only power/gnd conenction found {node}")

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
            logger.info("unmatched ports found")
            return 0

class WriteSpice:
    """ write hierarchical verilog file """

    def __init__(self, circuit_graph, circuit_name, inout_pin_names,subckt_list, lib_names):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = inout_pin_names
        self.subckt_list = subckt_list
        self.lib_names = lib_names
        self.all_mos = []
    def print_mos_subckt(self,fp,printed_mos):
        for mos in self.all_mos:
            if mos["name"] not in printed_mos:
                fp.write("\n.subckt " + mos["name"] + " D G S B")
                fp.write("\nm0 D G S1 B " + mos['model'] + ' '+ concat_values(mos["values"]))
                fp.write("\nm1 S1 G S B " + mos['model'] + ' '+ concat_values(mos["values"]))
                fp.write("\n.ends "+mos["name"]+'\n')
                printed_mos.append(mos["name"])
        return printed_mos

    def print_subckt(self, fp):
        logger.debug(f"Writing spice module : {self.circuit_name}")
        fp.write("\n.subckt " + self.circuit_name + " ")
        fp.write(' '.join(self.pins))

        for node, attr in self.circuit_graph.nodes(data=True):
            if 'source' in attr['inst_type']:
                continue
            if 'net' not in attr['inst_type']:
                if len(attr['inst_type'].split('_'))>2 and attr['inst_type'].split('_')[0]+'_'+attr['inst_type'].split('_')[1] in  self.lib_names:
                    self.all_mos.append({"name":attr['inst_type'], "model": 'nmos_rvt',"values": attr['values']})
                    line= "\nx" + node + ' '
                elif attr['real_inst_type'] in ['cap', 'res', '']:
                    line= "\n" + node + ' '                    
                else:
                    line= "\n" + node + ' '
                ports = []
                nets = []
                if "ports_match" in attr:
                    logger.debug(f'Nets connected to ports: {attr["ports_match"]}')
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
                    #move body pin to last
                    ports.append(ports.pop(0))
                    nets.append(nets.pop(0))
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
                elif "connection" in attr:
                    try:
                        logger.debug(f'connection to ports: {attr["connection"]}')
                        for key, value in attr["connection"].items():
                            if check_ports_match(self.subckt_list,key,attr['inst_type']):
                                ports.append(key)
                                nets.append(value)
                    except:
                        logger.error(f"ERROR: Subckt {attr['inst_type']} defination not found")

                else:
                    logger.error(f"No connectivity info found : {', '.join(attr['ports'])}")
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                line +=' '.join(nets) +' '+ attr['inst_type']
                fp.write(line)

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

def generate_lef(name, values, available_block_lef,
                 unit_size_mos=12 , unit_size_cap=12):
    """ Creates a shell script to generate parameterized lef"""
    logger.debug(f"checking lef for: {name}, {values}")
    #for param, value in size.items():

    if name.lower().startswith('cap'):
        #print("all val",values)
        if 'cap' in values.keys():
            size = float('%g'%(round(values["cap"]*1E15,4)))
            num_of_unit = float(size)/unit_size_cap
        elif 'c' in values.keys():
            size = float('%g'%(round(values["c"]*1E15,4)))
            num_of_unit = float(size)/unit_size_cap
        else:
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
            size = size.replace('.','p').replace('-','_neg_')
            num_of_unit=1
        logger.debug(f"Found cap with size: {size}, {unit_size_cap}")
        block_name = name + '_' + str(int(size)) + 'f'
        unit_block_name = 'Cap_' + str(unit_size_cap) + 'f'
        if block_name in available_block_lef:
            return block_name, available_block_lef[block_name]
        logger.debug(f'Generating lef for: {name}, {size}')
        if  num_of_unit > 128:
            return block_name, {
                'primitive': block_name,
                'value': int(size)
            }
        else:
            return unit_block_name, {
                'primitive': block_name,
                'value': unit_size_cap
            }


    elif name.lower().startswith('res'):
        if 'res' in values.keys():
            size = '%g'%(round(values["res"],2))
        elif 'r' in values.keys():
            size = '%g'%(round(values["r"],2))
        else :
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        block_name = name + '_' + size.replace('.','p')
        res_unit_size = 600
        try:
            #size = float(size)
            height = ceil(sqrt(float(size) / res_unit_size))
            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            logger.debug(f'Generating lef for: {block_name} {size}')
            return block_name, {
                'primitive': name,
                'value': (height, float(size))
            }
        except:
            return block_name, {
                'primitive': name,
                'value': (1, res_unit_size)
            }

    else:
        if "nfin" in values.keys():
            size = int(values["nfin"])
            if 'nf' in values.keys():
                size=size*int(values["nf"])
            ## Hack For VCO circuit
            if 'nmos' in name.lower() and unit_size_mos==37:
                unit_size_mos=8
            elif unit_size_mos==37:
                unit_size_mos=12
            no_units = ceil(size / unit_size_mos)

        elif "l" in values.keys():
            size = int(values["l"]*1E+9)
            no_units = ceil(size / unit_size_mos)

        else: 
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)

        logger.debug('Generating lef for: %s %s', name, str(size))
        if isinstance(size, int):
            no_units = ceil(size / unit_size_mos)
            if any(x in name for x in ['DP','_S']) and floor(sqrt(no_units/3))>=1:
                square_y = floor(sqrt(no_units/3))
            else:
                square_y = floor(sqrt(no_units))
            while no_units % square_y != 0:
                square_y -= 1
            yval = square_y
            xval = int(no_units / square_y)

            block_name = f"{name}_n{unit_size_mos}_X{xval}_Y{yval}"
            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            logger.debug("Generating parametric lef of: %s", block_name)
            return block_name, {
                'primitive': name,
                'value': unit_size_mos,
                'x_cells': xval,
                'y_cells': yval,
                'parameters': values
            }
        else:
            logger.debug("No proper parameters found for cell generation")
            block_name = name+"_"+size

    raise NotImplementedError(f"Could not generate LEF for {name}")


def check_ports_match(subckt_list,port,subckt):
    for members in subckt_list:
        if members["name"]==subckt and port in members["ports"]:
            return 1
        else:
            logger.info("ports match: %s %s",subckt,port)
            return 1

