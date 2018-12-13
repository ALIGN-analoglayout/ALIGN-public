# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 13:04:45 2018

@author: kunal
"""

# %% Parser

import networkx as nx
import os
#import re
import matplotlib.pyplot as plt
from collections import defaultdict
import itertools as it
from graphviz import Graph
from graphviz import Source
from BasicElement import BasicElement
from networkx.algorithms import bipartite
import json


class spiceParser:
    def __init__(self, netlistPath):
        self.netlist = netlistPath
        self.designTree = {}
        self.subckts = {}
        self.circuit_graph =nx.MultiGraph()
        self.params = []
        self.option = []
        self.top_insts = []
        self.include = []
        self.nets = defaultdict(list)

    def parser(self):
        if not os.path.isfile(self.netlist):
            print("File doesn't exist")
        else:
            print("File exist: ", self.netlist)
            fp = open(self.netlist, "r")
            line = fp.readline()
            while ".END" not in line:
                # if "**" in line.lower(): pass
                while line.strip().endswith('\\'):
                    #line.remove('\\')
                    line += fp.readline().strip()
                    #print(line)
                if any(c in line.lower() for c in ("//", "**")):
                    #line = fp.readline()
                    pass
                elif not line.strip():
                    pass
                elif "global" in line.lower():
                    global_line = line
                elif ".temp" in line.lower():
                    temp_line = line
                elif ".option" in line.lower():
                    self._parse_option(line, fp)
                elif ".subckt" in line.lower():
                    self._parse_subckt_info(line, fp)
                elif ".param" in line.lower():
                    self._parse_param(line, fp)
                elif "include" in line.lower() or "info" in line.lower():
                    self._parse_include(line, fp)
                    line = fp.readline()
                    continue
        
                else:
                    node1 = self._parse_inst(line)
                    if node1 != 'NULL':
                        self.top_insts.append(node1)
                line = fp.readline()
                if not line:
                    break
            print("PARSING FILE DONE")
            if self.params:
                self.params.remove('+')
                #print(" ".join(self.params))
            if self.params:
                self.option = filter(lambda a: a != '+', self.option)
                #print(" ".join(self.option))
            #print("Printing parsed netlist")


            self.subckts["__top__"] = {"ports": "NULL",
                                       "nodes": self.top_insts}
            FLAT=0
            if FLAT:
                Design = self._flatten_circuit("__top__")
            else:
                Design = self._hier_circuit("__top__")

            for subckt, elements in self.subckts.items():
                subckt_ports = ' '.join(elements["ports"])
                #print(subckt + ' ' + subckt_ports)
            #for element in elements["nodes"]:
            #    print(element)
            #for element in flatDesign:
                #print(element)
            self.circuit_graph = self._create_bipartite_circuit_graph(Design,subckt_ports)
            #self._show_circuit_graph("circuit", self.circuit_graph)
            return self.circuit_graph 
    def _parse_subckt_info(self, line, fp):
        subckt_nodes = line.strip().split()
        subckt_name = subckt_nodes[1]
        line = fp.readline()
        self.subckts[subckt_name] = {"ports": subckt_nodes[2:],
                                     "nodes": self._parse_subckt(line, fp)
                                     }

    def _parse_subckt(self, line, fp):
        insts = []
        while "end" not in line.lower():
            if any(c in line.lower() for c in ("//", '*')):
                line = fp.readline()
                pass
            # print("subckt: ", line)
            node1 = self._parse_inst(line)
            if node1 != 'NULL':
                insts.append(node1)
            line = fp.readline()
            while line.strip().endswith('\\'):
                #line.remove('\\')
                line += fp.readline().strip()
                #print(line)
        return insts

    def _parse_param(self, line, fp):
        while line.strip():
            # print("param: ", line)
            self.params += line.strip().split()
            line = fp.readline()

    def _parse_include(self, line, fp):
        #print(line)
        self.include.append(line.strip())
        line = fp.readline()
            
    def _parse_option(self, line, fp):
        while line.strip():
            # print("option: ", line)
            self.option += line.strip().split()
            line = fp.readline()

    def _parse_inst(self, line):
        element = BasicElement(line)
        device = "NULL"
        if line.strip().lower().startswith('m'):
            #print("transistor:", line)
            device = element.Transistor()
        elif line.strip().lower().startswith('v'):
            #print("vsource:", line)
            device = element.Vsource()
        elif line.strip().lower().startswith('e'):
            #print("vsource:", line)
            device = element.VCVSsource()
        elif line.strip().lower().startswith('i'):
            #print("Cur_source:", line)
            device = element.Isource()
        elif line.strip().lower().startswith('c'):
            #print("cap:", line)
            device = element.Capacitor()
        elif line.strip().lower().startswith('r'):
            #print("resistance:", line)
            device = element.Resistor()
        elif line.strip().lower().startswith('x'):
            hier_nodes = line.strip().split()
            device = {"inst": hier_nodes[0][1:],
                      "inst_type": hier_nodes[-1],
                      "ports": hier_nodes[1:-1],
                      "edge_weight": list(range(len(hier_nodes[1:-1]))),               
                      "values": "NULL"}
            #print("hier_Inst", line)
        else:
            return device
            print("not identified", line)
        return device

    def _flatten_circuit(self, subckt_name, subckt_inst=""):
        flatDesign = []
        print("flattening the circuits below "+subckt_name)
        for node in self.subckts[subckt_name]["nodes"]:
            if node["inst_type"] in self.subckts:
                flatDesign.extend(self._flatten_circuit(node["inst_type"],
                                      node["inst"]+'|')
                                )
            else:
                node["inst"] = subckt_inst+node["inst"]
                modified_ports = []
                for port in node["ports"]:
                    if port not in self.subckts[subckt_name]["ports"]:
                        port = subckt_inst+port
                    modified_ports.append(port)
                node["ports"] = modified_ports
                flatDesign.append(node)
        return flatDesign
    def _calc_edge_weight(self,subckt_name):
        edge_weight=[]
        for port in  self.subckts[subckt_name]["ports"]:
            weight =0
            for node in self.subckts[subckt_name]["nodes"]: 
                for i,sub_port in enumerate(node["ports"]):
                    if port == sub_port:
                        #print(sub_node)
                        weight +=  sub_node["edge_weight"][i]
            edge_weight.append(weight)

                    
    def _hier_circuit(self, subckt_name):
        hierDesign = []
        #print("making hierarchical circuits"+subckt_name)
        for node in self.subckts[subckt_name]["nodes"]:
            if node["inst_type"] in self.subckts:
                edge_weight =[]
                for port in  node["ports"]:
                    weight =0 
                    for sub_node in self.subckts[node["inst_type"]]["nodes"]:
                        #if sub_node["inst_type"] in self.subckts:
                        #    hier_nodes_list = self._hier_circuit(node["inst_type"])
                            
                        #self._hier_circuit(sub_node["inst_type"])
                        for i,sub_port in enumerate(sub_node["ports"]):
                            if port == sub_port:
                                #print(sub_node)
                                weight +=  sub_node["edge_weight"][i]
                    
                    edge_weight.append(weight)
                hier_node = {"inst": node["inst"],
                      "inst_type": node["inst_type"],
                      "ports": node["ports"],
                      "values": "NULL",
                      "edge_weight" :edge_weight,
                      "hier_nodes": self._hier_circuit(node["inst_type"])}
                hierDesign.append(hier_node)
            else:
                hierDesign.append(node)
        return hierDesign
    def _create_bipartite_circuit_graph(self, all_nodes,inout_ports):
        circuit_graph = nx.MultiGraph()
        for node in all_nodes:
            if "hier_nodes" in node.keys():
                #print("HIER NODE")
                subgraph = self._create_bipartite_circuit_graph(node["hier_nodes"],
                                                            node["ports"])
            else:
                subgraph="NULL"
            circuit_graph.add_node(node["inst"],
                                        inst_type=node["inst_type"],
                                        ports=node['ports'],
                                        edge_weight=node['edge_weight'],
                                        values=node['values'],
                                        sub_graph=subgraph
                                        )
            wt_index=0
            for net in node["ports"]:
                #if net not in ["0", "vdd!", "gnd!"]:
                if net not in circuit_graph:
                    if net in inout_ports:                    
                        circuit_graph.add_node(net,inst_type="net", net_type="external")
                    else:
                        circuit_graph.add_node(net,inst_type="net", net_type="internal")

                wt = node["edge_weight"][wt_index]
                circuit_graph.add_edge(node["inst"], net,weight=wt)
                wt_index +=1
        return circuit_graph
        #return self.circuit_graph
    '''
    def _create_circuit_graph(self, all_nodes):
        for node in all_nodes:
            self.circuit_graph.add_node(node["inst"],
                                        inst_type=node["inst_type"])
            for net in node["ports"]:
                if net not in self.circuit_graph:
                    if net not in ["0", "vdd!", "gnd!"]:
                        self.circuit_graph.add_node(net,inst_type="net")    
                        self.circuit_graph.add_edge(node, net, name=net)
        return self.circuit_graph
    '''
    def _show_circuit_graph(self,filename, graph):
        for subgraph in nx.connected_component_subgraphs(graph):
            color_map = []
            X, Y = bipartite.sets(subgraph)
            pos = dict()
            pos.update( (n, (1, i)) for i, n in enumerate(X) ) # put nodes from X at x=1
            pos.update( (n, (2, i)) for i, n in enumerate(Y) ) # put nodes from Y at x=2
            #nx.draw(B, pos=pos)
            #plt.show()
            plt.figure(figsize=(6, 8))
            for x, y in subgraph.nodes(data=True):
                if "inst_type" in y:
                    if y["inst_type"] == 'pmos':
                        color_map.append('red')
                    elif y["inst_type"] == 'nmos':
                        color_map.append('cyan')
                    elif y["inst_type"] == 'cap':
                        color_map.append('orange')
                    elif y["inst_type"] == 'net':
                        color_map.append('pink')
                    else:
                        color_map.append('green')
            nx.draw(subgraph, node_color=color_map,
                             with_labels=True,pos=pos)
            plt.title(filename,fontsize=20)
            #plt.savefig(".png")
            #plt.show()
            #self._laplacian_matrix(subgraph)
            #nx.nx_pydot.write_dot(subgraph, filename+'.dot')
            if not os.path.exists("circuit_graphs"):
                os.mkdir("circuit_graphs")
            nx.write_yaml(subgraph,"circuit_graphs/"+filename+".yaml")
    '''
    def _show_circuit_graph(self,subckt_name, graph):
        for subgraph in nx.connected_component_subgraphs(graph):
            color_map = []
            for x, y in subgraph.nodes(data=True):
                if "inst_type" in y:
                    if y["inst_type"] == 'pmos':
                        color_map.append('red')
                    elif y["inst_type"] == 'nmos':
                        color_map.append('blue')
                    elif y["inst_type"] == 'cap':
                        color_map.append('orange')
                    else:
                        color_map.append('green')
            path = subckt_name+'.dot'
            if os.path.exists(path):
                print("removing existing dot file")
                os.remove(path)
                try:
                    os.remove(path+'.pdf')
                except OSError:
                    print("cannot remove {}.pdf file".format(path))            
            nx.nx_pydot.write_dot(subgraph, path)
            s = Source.from_file(path)
            s.view()
    '''
    def _laplacian_matrix(self, graph):
        L = nx.laplacian_matrix(graph, nodelist=None, weight='weight')
        print(L)



# %% all graphs
if __name__ == '__main__':
    netlist_dir = "input_circuit/"
    netlist_files = os.listdir(netlist_dir)
    #output_dir ='train_nodes/'
    for netlist in netlist_files:
        print (netlist)
        #name = "switched_cap_filter"
        #netlistPath = netlistir+name+".netlist"
        #if  netlist.endswith('netlist') or netlist.endswith('sp'):
        if "switched_cap_filter" in netlist :
            sp = spiceParser(netlist_dir+netlist)
            circuit_graph = sp.parser()
            sp._show_circuit_graph( netlist.split('.')[0],circuit_graph)
#            sp._laplacian_matrix(circuit_graph)
#            with open(output_dir+netlist+'.txt', 'w') as handle:
#                for node,attr in graph.nodes(data=True):
#                    handle.write("\n"+node+','+attr["inst_type"])
