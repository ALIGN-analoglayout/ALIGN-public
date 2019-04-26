# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
import pickle
import os
import logging
import argparse
from math import sqrt, ceil
from read_lef import read_lef

#if not os.path.exists("./LOG"):
#    os.mkdir("./LOG")
#logging.basicConfig(filename='./LOG/writer.log', level=logging.DEBUG)


class WriteVerilog:
    """ write hierarchical verilog file """
    def __init__(self, circuit_graph, circuit_name, inout_pin_names):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = inout_pin_names

    def print_module(self, fp):
        logging.info("Writing module : %s", self.circuit_name)
        fp.write("\nmodule " + self.circuit_name + " ( ")
        fp.write(', '.join(self.pins))
        fp.write(" ); ")

        if self.inout_pins:
            logging.info("Writing ports : %s", ', '.join(self.inout_pins))
            fp.write("\ninout ")
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
                    logging.info("Nets connected to ports: %s",
                                 ', '.join(attr["ports_match"].values()))
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
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


def generate_lef(fp, name, size, available_block_lef, unit_size=10):
    """ Creates a shell script to generate parameterized lef"""
    #print(name,size)
    for param,value in size.items():
        if 'fin' in param.lower():
            size = int(value)*2
            logging.info('Generating lef for: %s %i', name, size)
            no_units = ceil(size / unit_size)
            square_x = ceil(sqrt(no_units))
            while no_units % square_x != 0:
                square_x += 1
            xval = str(square_x)
            yval = str(int(no_units / square_x))
            block_name = name + "_n" + str(unit_size) + "_X" + xval + "_Y" + yval
            if block_name in available_block_lef:
                return block_name
            logging.info("Generating parametric lef of: %s", block_name)
            fp.write("\npython fabric_" + name + ".py " + " -b " + block_name + " -n " +
                     str(unit_size) + " -X " + xval + " -Y " + yval)
        elif 'cap' in param.lower():
            size = int(value)
            cap_unit_size=unit_size
            block_name = name+'_'+str(value)+'f'
            unit_block_name =param+'_'+str(cap_unit_size)+'f' 
            if block_name in available_block_lef:
                return block_name
            logging.info('Generating lef for: %s %s', name, size)
            fp.write("\npython fabric_" + name + ".py " + " -b " + unit_block_name + " -n " + str(cap_unit_size))
        elif 'res' in param.lower():
            size = int(value)
            res_unit_size=30*unit_size
            height=ceil(sqrt(size/res_unit_size))
            block_name = name+'_'+str(size)
            if block_name in available_block_lef:
                return block_name
            logging.info('Generating lef for: %s %s', block_name, size)
            fp.write("\npython fabric_" + name + ".py " + " -b " + block_name + " -n " + str(height) + " -r "+ str(size)) 



    return block_name


#%%
if __name__ == '__main__':
    RESULT_DIR = "./results/"
    logging.info("Writing results in ./results dir: ")

    PARSER = argparse.ArgumentParser(
        description="directory path for input circuits")
    PARSER.add_argument("-U",
                        "--unit_size",
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
    INPUT_PICKLE = INPUT_PICKLE[0]
    logging.info("Picking first file for generating results: %s", INPUT_PICKLE)
    # write a verilog file
    VERILOG_FP = open(RESULT_DIR + INPUT_PICKLE + '.v', 'w')
    LEF_FP = open(RESULT_DIR + INPUT_PICKLE + '_lef.sh', 'w')
    LEF_FP.write('# file to generate lef')
    print_header(VERILOG_FP, INPUT_PICKLE)
    POWER_PINS = ["VDD", "VSS"]
    #read lef to not write those modules as macros
    ALL_LEF = read_lef()
    logging.info("Reading available lef: %s", ", ".join(ALL_LEF))

    UNIT_SIZE = ARGS.unit_size
    logging.info("Unit cell size: %s", str(UNIT_SIZE))
    logging.info("Reading file: %s", RESULT_DIR + INPUT_PICKLE + '.p')

    with open(RESULT_DIR + INPUT_PICKLE + '.p', 'rb') as fp:
        list_graph = pickle.load(fp)
    #print(list_graph)
    for members in list_graph:
        #print(members)
        name = members["name"]
        logging.info("Found module: %s", name)
        if 'ports_match' in members.keys():
            logging.info("Ports in module: %s",
                         ", ".join(members['ports_match']))

        graph = members["lib_graph"].copy()
        logging.info("Reading nodes from graph: %s", str(graph))
        for node, attr in graph.nodes(data=True):
            #lef_name = '_'.join(attr['inst_type'].split('_')[0:-1])
            if 'net' in attr['inst_type']: continue
            lef_name = attr['inst_type']
            if "values" in attr and (lef_name in ALL_LEF):
                block_name = generate_lef(LEF_FP, lef_name, attr["values"],
                                          ALL_LEF, UNIT_SIZE)
                logging.info("Created new lef for: %s", block_name)
                ALL_LEF.append(block_name)
                graph.nodes[node]['inst_type'] = block_name
            else:
                logging.info("ERROR:No physical information found for: %s", name)

        if name in ALL_LEF:
            continue
        if "ports" in members.keys():
            inoutpin = members["ports"]
        elif "ports_match" in members.keys():
            inoutpin = members["ports_match"]
        else:
            inoutpin = []
        #print("inout pins:",inoutpin)
        logging.info("writing verilog for block: %s", name)
        wv = WriteVerilog(graph, name, inoutpin)
        wv.print_module(VERILOG_FP)
    LEF_FP.close()

    print("OUTPUT LEF generator:", RESULT_DIR + INPUT_PICKLE + "_lef.sh")
    print_globals(VERILOG_FP, POWER_PINS)
    print("OUTPUT verilog netlist at:", RESULT_DIR + INPUT_PICKLE + ".v")
