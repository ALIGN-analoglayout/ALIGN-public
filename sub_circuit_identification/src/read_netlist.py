# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 13:04:45 2018

@author: kunal
"""

# %% Parser

import os
import argparse
import logging
import networkx as nx

from util import _write_circuit_graph, _show_circuit_graph
from basic_element import _parse_inst

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
elif os.path.exists("./LOG/read_netlist.log"):
    os.rename("./LOG/read_netlist.log", "./LOG/read_netlist.log1")

logging.basicConfig(filename='./LOG/read_netlist.log', level=logging.DEBUG)


class SpiceParser:
    """
    Read a spice file (.sp/.cdl) and converts it to a graph.
    Device properties are inherited from BasicElement.py
    You can flatten the circuit by using flag: flat
    The final graph is stored in a yaml file in circuit_graphs folder.
    """

    def __init__(self, netlistPath, top_ckt_name='__top__', flat=1):
        self.netlist = netlistPath
        self.subckts = {}
        self.circuit_graph = nx.Graph()
        self.params = []
        self._global = []
        self.option = []
        self.top_insts = []
        self.include = []
        self.top_ckt_name = top_ckt_name
        self.flat = flat
        logging.info('creating an instance of SpiceParser')

    def sp_parser(self):

        """Parse the defined file line wise"""

        if not os.path.isfile(self.netlist):
            print("File doesn't exist")
        else:
            logging.info("File exist: %s", self.netlist)
            fp_l = open(self.netlist, "r")
            line = fp_l.readline()
            while ".END" not in line:
                # if "**" in line.lower(): pass
                while line.strip().endswith('\\'):
                    line += fp_l.readline().strip()
                if any(c in line.lower() for c in ("//", "**")):
                    #line = fp_l.readline()
                    pass
                elif not line.strip():
                    pass
                elif "global" in line.lower():
                    self._parse_global(line, fp_l)
                elif ".temp" in line.lower():
                    temp_line = line
                elif ".option" in line.lower():
                    self._parse_option(line, fp_l)
                elif "subckt" in line.lower():
                    self._parse_subckt_info(line, fp_l)
                elif ".param" in line.lower():
                    self._parse_param(line, fp_l)
                elif "include" in line.lower() or "info" in line.lower():
                    self._parse_include(line, fp_l)
                    line = fp_l.readline()
                    continue

                else:
                    parsed_inst = _parse_inst(line)
                    if parsed_inst:
                        self.top_insts.append(parsed_inst)
                line = fp_l.readline()
                if not line:
                    break
            print("INFO: PARSING INPUT NETLIST FILE DONE")
            if self.params:
                #self.params.remove('+')
                self.params = filter(lambda a: a != '+', self.params)
                #logging.info(" ".join(self.params))
            elif self.option:
                self.option = filter(lambda a: a != '+', self.option)
                #logging.info(" ".join(self.option))
            elif self._global:
                self._global = filter(lambda a: a != '+', self._global)

            if self.top_ckt_name == '__top__':
                top = os.path.basename(self.netlist).split('.')[0]
                logging.info('NO subckt defined, \
                        checking for any instance at top')
                logging.info("picking subckt name as filename: %s", top)

                if not self.top_insts:
                    if top in self.subckts.keys():
                        self.top_ckt_name = os.path.basename(
                            self.netlist).split('.')[0]
                        logging.info(
                            'No top instances found. Picking filename as top: %s',
                            self.top_ckt_name)

                    elif self.subckts.keys():
                        self.top_ckt_name = list(self.top_ckt_name())[0]
                        logging.info(
                            'No top instances found. Picking 1st cirucit as top: %s'
                            , self.top_ckt_name)
                    else:
                        logging.info(
                            'No subckt found in design. Please check file format'
                        )
                        return 0
                else:
                    logging.info(
                        'Instances found at top, creating a dummy __top__ subckt'
                    )
                    self.top_ckt_name = top
                    self.subckts[self.top_ckt_name] = {
                        "ports": ["gnd!", "vdd"],
                        "nodes": self.top_insts
                    }

                logging.info("List of subckts in design: %s", " ".join(self.subckts))

            if self.flat:
                logging.info("Flaten circuit:%s ", self.top_ckt_name)
                design = self._flatten_circuit(self.top_ckt_name)
            else:
                design = self._hier_circuit(self.top_ckt_name)

            subckt_ports = self.subckts[self.top_ckt_name]["ports"]

            self.circuit_graph = self._create_bipartite_circuit_graph(
                design, subckt_ports)
            #self._show_circuit_graph("circuit", self.circuit_graph,"./circuit_graph_images/")
            return self.circuit_graph

    def _parse_subckt_info(self, line, fp_l):
        """ Read subckt line """
        logging.info('started reading subckt: %s', line)
        subckt_nodes = line.strip().split()
        subckt_name = subckt_nodes[1]
        line = fp_l.readline()
        while line.strip().endswith('\\'):
            line += fp_l.readline().strip()
        self.subckts[subckt_name] = {
            "ports": subckt_nodes[2:],
            "nodes": self._parse_subckt(line, fp_l)
        }
        logging.info('Finished reading subckt: %s', subckt_name)

    def _parse_subckt(self, line, fp_l):
        """ Read all lines in subckt"""
        insts = []
        while not (line.lower().startswith('end') or
                   line.lower().startswith('.end')):
            if any(c in line.lower() for c in ("//", '*')):
                line = fp_l.readline()
                pass
            node1 = _parse_inst(line)
            if node1:
                insts.append(node1)
            line = fp_l.readline()

            while line.strip().endswith('\\'):
                line += fp_l.readline().strip()

        return insts

    def _parse_param(self, line, fp_l):
        """Reads and store all parameters"""
        while line.strip():
            logging.info("param: %s", line)
            self.params += line.strip().split()
            line = fp_l.readline()

    def _parse_global(self, line, fp_l):
        """ Read all global lines"""
        while line.strip():
            logging.info("global: %s", line)
            self._global += line.strip().split()
            line = fp_l.readline()

    def _parse_include(self, line, fp_l):
        logging.info("include: %s", line)
        self.include.append(line.strip())
        line = fp_l.readline()

    def _parse_option(self, line, fp_l):
        while line.strip():
            logging.info("option: %s", line)
            self.option += line.strip().split()
            line = fp_l.readline()



    def _flatten_circuit(self, subckt_name, subckt_inst="", connected_nets=""):
        flatdesign = []
        logging.info("flattening the circuits below: %s", subckt_name)
        for node in self.subckts[subckt_name]["nodes"]:
            modified_ports = []
            for net_name in node["ports"]:
                if net_name not in self.subckts[subckt_name]["ports"]:
                    logging.info("Net internal to subckt")
                    net_name = subckt_inst + net_name
                elif connected_nets:
                    logging.info("Net is part of higher level subckt")
                    net_name = connected_nets[self.subckts[subckt_name]
                                              ["ports"].index(net_name)]
                else:
                    logging.info("net lies in top level net in: %s net_name: %s",
                                 node["inst"], net_name)
                modified_ports.append(net_name)

            if node["inst_type"] in self.subckts:

                flatdesign.extend(
                    self._flatten_circuit(node["inst_type"],
                                          subckt_inst + node["inst"] + '|',
                                          list(modified_ports)))
            else:
                flat_node = {
                    "inst": subckt_inst + node["inst"],
                    "inst_type": node["inst_type"],
                    "ports": modified_ports,
                    "values": node["values"],
                    "edge_weight": node["edge_weight"]
                }

                flatdesign.append(flat_node)
                logging.debug("Node name: %s, type: %s", flat_node["inst"],
                              flat_node["inst_type"])

        logging.info("Total no of nodes in design %s = %i", subckt_name,
                     len(flatdesign))
        return flatdesign

    def _hier_circuit(self, subckt_name):
        hier_design = []
        logging.info("making hierarchical circuits: %s", subckt_name)
        for node in self.subckts[subckt_name]["nodes"]:
            if node["inst_type"] in self.subckts:
                logging.info("FOUND hier_node: %s", node["inst_type"])
                hier_node = {
                    "inst": node["inst"],
                    "inst_type": node["inst_type"],
                    "ports": node["ports"],
                    "values": None,
                    "edge_weight": node["edge_weight"],
                    "hier_nodes": self._hier_circuit(node["inst_type"])
                }
                hier_design.append(hier_node)
            else:
                hier_design.append(node)
        return hier_design

    def _create_bipartite_circuit_graph(self, all_nodes, inout_ports):
        logging.info("Creating bipartitie graph with Total no of devices %i",
                     len(all_nodes))
        circuit_graph = nx.Graph()
        for node in all_nodes:
            if "hier_nodes" in node.keys():
                subgraph = self._create_bipartite_circuit_graph(
                    node["hier_nodes"],
                    self.subckts[node["inst_type"]]["ports"])
            else:
                subgraph = None
            circuit_graph.add_node(node["inst"],
                                   inst_type=node["inst_type"],
                                   ports=node['ports'],
                                   edge_weight=node['edge_weight'],
                                   values=node['values'],
                                   sub_graph=subgraph)
            wt_index = 0
            for net in node["ports"]:
                #if net not in ["0", "vdd!", "gnd!"]:
                if "edge_weight" in node.keys():
                    edge_wt = node["edge_weight"][wt_index]
                else:
                    edge_wt = 2 ^ wt_index
                if net not in circuit_graph:
                    if net in inout_ports:
                        circuit_graph.add_node(net,
                                               inst_type="net",
                                               net_type="external")
                    else:
                        circuit_graph.add_node(net,
                                               inst_type="net",
                                               net_type="internal")
                elif circuit_graph.has_edge(node["inst"], net):
                    node_name = node["inst"]
                    edge_wt += circuit_graph.get_edge_data(node_name, net)['weight']
                circuit_graph.add_edge(node["inst"], net, weight=edge_wt)
                wt_index += 1
        return circuit_graph



#%%%%%%%%%%%%%%%%%%%%%%%%%MAIN%%%%%%%%%%%%%%%%%%%%
if __name__ == '__main__':

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
        default=1,
        help='1 = flatten the netlist, 0= read as hierahical netlist')
    ARGS = PARSER.parse_args()
    NETLIST_DIR = ARGS.dir
    if not os.path.isdir(NETLIST_DIR):
        logging.info("Input dir doesn't exist. Please enter a valid dir path")
        print("Input dir doesn't exist. Please enter a valid dir path")

    NETLIST_FILES = os.listdir(NETLIST_DIR)
    if not NETLIST_FILES:
        print("No spice files found in input_circuit directory. exiting")
        logging.info("No spice files found in input_circuit directory. exiting")
        exit(0)
    elif ARGS.file:
        logging.info("Input file: %s", ARGS.file)
        NETLIST_FILES = [ARGS.file]
    for netlist in NETLIST_FILES:
        print(netlist)
        #name = "switched_cap_filter"
        if netlist.endswith('sp') or netlist.endswith('cdl') or ARGS.file:
            logging.info("READING files in dir: %s", NETLIST_DIR)
            logging.info("READ file: %s/%s flat=%i", NETLIST_DIR, netlist, ARGS.flat)
            if ARGS.subckt and ARGS.flat ==0:
                logging.info("Reading subckt %s as flat",ARGS.subckt)
                sp = SpiceParser(NETLIST_DIR + '/' + netlist,
                                 ARGS.subckt,
                                 flat=ARGS.flat)
            elif ARGS.subckt:
                sp = SpiceParser(NETLIST_DIR + '/' + netlist, ARGS.subckt)
            elif ARGS.flat:
                logging.info("Reading netlist as flat")
                sp = SpiceParser(NETLIST_DIR + '/' + netlist, flat=ARGS.flat)
            else:
                sp = SpiceParser(NETLIST_DIR + '/' + netlist)

            final_circuit_graph = sp.sp_parser()
            if final_circuit_graph:
                ckt_name = netlist.split('.')[0]
                logging.info("Saving graph: %s", ckt_name)
                _show_circuit_graph(ckt_name, final_circuit_graph,"./circuit_graph_images/")
                #_show_bipartite_circuit_graph( netlist.split('.')[0],final_circuit_graph, "./circuit_graphs/")
                _write_circuit_graph(ckt_name, final_circuit_graph, "./circuit_graphs/")
        else:
            print("Not a valid file type (.sp/cdl).Skipping this file")
