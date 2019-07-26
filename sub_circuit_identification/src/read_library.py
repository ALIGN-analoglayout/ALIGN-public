# -*- coding: utf-8 -*-
"""
Created on Fri Oct 12 11:40:29 2018

@author: kunal
"""
# %% sp_parser

import os
import argparse
import logging
import networkx as nx

from util import _write_circuit_graph, _show_circuit_graph
from basic_element import _parse_inst

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
logging.basicConfig(filename='./LOG/read_library.log', level=logging.DEBUG)


class SpiceParser:
    """
    Read a spice file (.sp/.cdl) and converts it to a graph.
    Device properties are inherited from BasicElement.py
    You can flatten the circuit by using flag: flat
    The final graph is stored in a yaml file in circuit_graphs folder.
    """

    def __init__(self, netlistPath):
        self.netlist = netlistPath
        self.flat_design = []
        self.subckts = {}
        self.params = []
        self._global = []
        self.option = []
        self.top_insts = []

    def sp_parser(self):
        """Parse the defined file line wise"""
        if not os.path.isfile(self.netlist):
            print("File doesn't exist")
        else:
            logging.info("File exist: %s", self.netlist)
            fp_l = open(self.netlist, "r")
            line = fp_l.readline()
            while ".END" not in line:
                # if "**" in line.lower(): pass comment line
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
            print("INFO: PARSING LIBRARY FILE DONE")
            if self.params:
                #self.params.remove('+')
                self.params = filter(lambda a: a != '+', self.params)
                #logging.info(" ".join(self.params))
            elif self.option:
                self.option = filter(lambda a: a != '+', self.option)
                #logging.info(" ".join(self.option))
                #logging.info("Printing parsed netlist")
            elif self._global:
                self._global = filter(lambda a: a != '+', self._global)

            #print("Printing parsed netlist")

            for subckt_name, elements in self.subckts.items():
                subckt_ports = ' '.join(elements["ports"])
                subckt_graph = self._create_bipartite_circuit_graph(
                    elements["nodes"], subckt_ports)
                self.subckts[subckt_name]['node_graph'] = subckt_graph
                logging.info("Saving graph: %s", subckt_name)
                #_show_circuit_graph(subckt_name, subckt_graph, "./library_graph_images/")
                _write_circuit_graph(subckt_name, subckt_graph,
                                     "./library_graphs/")
                fp_l.close()

    def _merge_stacked_transistor(self, ckt_graph):
        #ckt_graph_copy = ckt_graph.copy()
        for node, attr in ckt_graph.nodes(data=True):
            if "net" in ckt_graph.nodes[node]["inst_type"]:
                #print(ckt_graph.nodes(node))
                if ckt_graph.edges[node]["weight"] >= 4:
                    print("gate net in graph ", node,
                          ckt_graph.neighbors(node))

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
        while not (line.lower().startswith('end')
                   or line.lower().startswith('.end')):
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

    def _flatten_circuit(self, subckt_name, subckt_inst=""):
        print("flattening the circuits below " + subckt_name)
        for node in self.subckts[subckt_name]["nodes"]:
            if node["inst_type"] in self.subckts:
                self._flatten_circuit(node["inst_type"], node["inst"] + '|')
            else:
                node["inst"] = subckt_inst + node["inst"]
                modified_ports = []
                for port in node["ports"]:
                    if port not in self.subckts[subckt_name]["ports"]:
                        port = subckt_inst + port
                    modified_ports.append(port)
                node["ports"] = modified_ports
                self.flat_design.append(node)

    def _create_bipartite_circuit_graph(self, all_nodes, inout_ports):
        logging.info("Creating bipartitie graph with Total no of devices %i",
                     len(all_nodes))
        circuit_graph = nx.Graph()
        circuit_graph.clear()
        for node in all_nodes:
            if not node: continue
            circuit_graph.add_node(node["inst"],
                                   inst_type=node["inst_type"],
                                   ports=node['ports'],
                                   edge_weight=node['edge_weight'],
                                   values=node['values'])
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
                    edge_wt += circuit_graph.get_edge_data(node_name,
                                                           net)['weight']
                circuit_graph.add_edge(node["inst"], net, weight=edge_wt)
                wt_index += 1
        return circuit_graph


#%%%%%%%%%%%%%%%%%%%%%%%%%LIBRARY%%%%%%%%%%%%%%%%%%%%
if __name__ == '__main__':
    PARSER = argparse.ArgumentParser(
        description="directory path for library circuits")
    PARSER.add_argument("-d",
                        "--dir",
                        type=str,
                        default='./basic_library/',
                        help='relative directory path')
    ARGS = PARSER.parse_args()
    LIB_DIR = ARGS.dir
    for lib_file in os.listdir(LIB_DIR):
        if lib_file.endswith(".sp"):
            fp = os.path.join(LIB_DIR, lib_file)
            print("Reading library file: ", fp)
            sp = SpiceParser(fp)
            sp.sp_parser()
    print("Reading Library Successful. Graphs are stored in library_graphs")
