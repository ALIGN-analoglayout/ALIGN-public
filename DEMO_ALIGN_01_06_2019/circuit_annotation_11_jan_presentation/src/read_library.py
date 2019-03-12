# -*- coding: utf-8 -*-
"""
Created on Fri Oct 12 11:40:29 2018

@author: kunal
"""
# %% Parser

import networkx as nx
import os,glob
#import re
import matplotlib.pyplot as plt
from collections import defaultdict
import itertools as it
from networkx.algorithms import bipartite
from itertools import combinations 


from BasicElement import BasicElement

class spiceParser:
    def __init__(self, netlistPath):
        self.netlist = netlistPath
        self.designTree = {}
        self.flatDesign = []
        self.subckts = {}
        self.params = []
        self.option = []
        self.top_insts = []

    def parser(self):
        if not os.path.isfile(self.netlist):
            print("File doesn't exist")
        else:
            print("File exist: ", self.netlist)
            fp = open(self.netlist, "r")
            line = fp.readline()
            while ".END" not in line:
                # if "*" in line.lower(): pass comment line
                if any(c in line.lower() for c in ("//", '*')):
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
                else:
                    parsed_inst=self._parse_inst(line)
                    self.top_insts.append(parsed_inst)
                    #print(parsed_inst)
                line = fp.readline()
                if not line:
                    break
            print("PARSING FILE DONE")
            if self.params:
                if '+' in self.params:
                    self.params.remove('+')
                    print(" ".join(self.option))


            if self.params:
                self.option = filter(lambda a: a != '+', self.option)
                #print(" ".join(self.params))
      
            #print("Printing parsed netlist")

            for subckt_name, elements in self.subckts.items():
                subckt_ports = ' '.join(elements["ports"])
                #print(subckt_name + ' ' + subckt_ports)
                #print(elements)
                #elements = filter(None, elements)

                #subckt_graph = self._create_bipartite_circuit_graph(subckt_name,
                #                                          elements["nodes"])
                subckt_graph = self._create_bipartite_circuit_graph(subckt_name,
                                                          elements["nodes"],subckt_ports)
                #self._merge_stacked_transistor(subckt_graph)
                self.subckts[subckt_name]['node_graph'] = subckt_graph
                
                #if "L2_WSCCM" == subckt_name:
                #nx.draw(subckt_graph)
                #show_circuit_graph(subckt_name, subckt_graph)
                #self._show_circuit_graph(subckt_graph)
                self._show_circuit_graph( subckt_name,subckt_graph)
                fp.close()
    def _merge_stacked_transistor(self,ckt_graph):
        ckt_graph_copy=ckt_graph.copy()
        for node, attr in ckt_graph.nodes(data=True):
            if "net" in ckt_graph.nodes[node]["inst_type"]:
                #print(ckt_graph.nodes(node))
                if ckt_graph.edges[node]["weight"] >=4:
                    print("gate net in graph ",node, ckt_graph.neighbors(node))
    '''
        #print("Is input bipartite",nx.is_bipartite(G))
        new_node=""
        ports={}
        subgraph = nx.MultiGraph()
        for node in argv:
            new_node +='_'+node
            subgraph.add_node(node, inst_type=G.nodes[node]["inst_type"])
            #print(G.nodes[node])
            nbr=G.neighbors(node)
            for ele in nbr:
                if ele not in subgraph.nodes():
                    subgraph.add_node(ele, inst_type=G.nodes[ele]["inst_type"])
                subgraph.add_edge(node, ele, weight=G[node][ele][0]["weight"])
                #print("adding edge b/w:",node,ele,G[node][ele][0]["weight"])
                
                if ele in ports:
                    ports[ele] += G[node][ele][0]["weight"]
                else:
                    ports[ele] = G[node][ele][0]["weight"]
            
            #G.add_edge(new_node,ele,weight=wt)
        G.add_node(new_node,inst_type=Htype)
        
        for pins in list(ports):
            if set (G.neighbors(pins)) <= set(argv):
                del ports[pins]
                print("deleting node",pins)
                G.remove_node(pins)
        for node in argv:
            G.remove_node(node)
        for pins in ports:
            G.add_edge(new_node,pins,weight=ports[pins])
        
    def _merge_stacked_transistor(self,all_nodes):
        print(len(all_nodes))
        for nodei,nodej in list(combinations(all_nodes, 2)):
            if nodei == 'NULL' or nodej == 'NULL':continue

            if (
                    nodei['ports'][1] == nodej['ports'][1] #and
                    #(nodei['ports'][0] == nodej['ports'][0] and
                     #nodei['ports'][2] == nodej['ports'][2]) #or
                    # (nodei['ports'][0] == nodej['ports'][2] and
                     #nodei['ports'][2] == nodej['ports'][0]) 
                     
                ):
                print("parallel transistors")
                print("nodei",nodei)
                print("nodej",nodej)
            
            if nodei != 'NULL' and 'mos' in nodei['inst_type'] :
    
            for nodej in all_nodes:
                    if nodej == 'NULL' :continue
                    if 'mos' in nodej['inst_type'] :
                        print(nodei['ports'],nodej['ports'])

            if node == 'NULL' :continue
            print("merging parallel  transistor")
            rem_nodes = [key for key in Gsub if 'mos' in G1.nodes[key]["inst_type"]]
            reduced_graph,subgraph = merge_nodes(G1,sub_blocks,rem_nodes)
            print(all_nodes)
            circuit_graph.add_node(node["inst"],
                                        inst_type=node["inst_type"])
            wt_index=0
            for net in node["ports"]:
                #if net not in ["0", "vdd!", "gnd!"]:
                if net not in circuit_graph:
                    circuit_graph.add_node(net,inst_type="net")
                if "edge_weight" in node.keys():
                    #print("setting weight")
                    wt = node["edge_weight"][wt_index] 
    '''
    def _parse_subckt_info(self, line, fp):
        subckt_nodes = line.strip().split()
        subckt_name = subckt_nodes[1]
        line = fp.readline()
        self.subckts[subckt_name] = {"ports": subckt_nodes[2:],
                                     "nodes": self._parse_subckt(line, fp)}

    def _parse_subckt(self, line, fp):
        insts = []
        while "end" not in line.lower():
            if any(c in line.lower() for c in ("//", '*')):
                line = fp.readline()
                pass
            # print("subckt: ", line)
            insts.append(self._parse_inst(line))
            line = fp.readline()
        return insts

    def _parse_param(self, line, fp):
        while line.strip():
            # print("param: ", line)
            self.params += line.strip().split()
            line = fp.readline()

    def _parse_option(self, line, fp):
        while line.strip():
            # print("option: ", line)
            self.option += line.strip().split()
            line = fp.readline()

    def _parse_inst(self, line):
        line = line.replace("(", "")
        line = line.replace(")", "")
        element = BasicElement(line)
        device = "NULL"
        #print(line)
        if line.strip().lower().startswith('m'):
            #print("transistor:", line)
            device = element.Transistor()
            #print(device)
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
                      "values": "NULL"}
            #print(device['ports'])
            #print("hier_Inst", line)
        else:
            print("not identified", line)
        return device

    def _flatten_circuit(self, subckt_name, subckt_inst=""):
        print("flattening the circuits below "+subckt_name)
        for node in self.subckts[subckt_name]["nodes"]:
            if node["inst_type"] in self.subckts:
                self._flatten_circuit(node["inst_type"],
                                      node["inst"]+'|')
            else:
                node["inst"] = subckt_inst+node["inst"]
                modified_ports = []
                for port in node["ports"]:
                    if port not in self.subckts[subckt_name]["ports"]:
                        port = subckt_inst+port
                    modified_ports.append(port)
                node["ports"] = modified_ports
                self.flatDesign.append(node)
    '''
    def _create_circuit_graph(self, subckt_name, all_nodes):
        ckt_graph = nx.MultiGraph()
        ckt_graph.clear()
        nets = defaultdict(list)

        for node in all_nodes:
            ckt_graph.add_node(node["inst"],
                                        inst_type=node["inst_type"])

            for net in node["ports"]:
                nets[net].append(node["inst"])
        for net, nodes in nets.items():
            if net not in ["0", "vdd!", "gnd!"]:
                weight1 =0 
                for pair in it.combinations(nodes, 2):
                    weight1 += self._calc_weight(pair,net,all_nodes)
                    ckt_graph.add_edge(*pair, name=net , weight = weight1)
                    
        print(ckt_graph.edges(data=True))
        return ckt_graph
        '''
    def _calc_weight(self,pair,net, all_nodes):
        weight = 1
        for node in all_nodes:
            if node["inst"]== pair[0]:
                for pos in range(len(node["ports"])):
                    if node["ports"][pos]==net:
                        weight *= 2^pos
                
            if node["inst"]== pair[1]:
                for pos in range(len(node["ports"])):
                    if node["ports"][pos]==net:
                        weight *= 2^pos
        return weight
    def _create_bipartite_circuit_graph(self, subckt_name, all_nodes,inout_ports):
        circuit_graph = nx.MultiGraph()
        circuit_graph.clear()
        #filter(NULL, all_nodes)
        for node in all_nodes:
            if node == 'NULL' :continue
            #print("CREATING BIPARTITE GRAPH")
            #print(all_nodes)
            #print(node)
            #print(node)
            circuit_graph.add_node(node["inst"],
                                        inst_type=node["inst_type"],
                                        ports=node['ports'],
                                        edge_weight=node['edge_weight'],
                                        values=node['values']
                                        )
            wt_index=0
            for net in node["ports"]:
                #if net not in ["0", "vdd!", "gnd!"]:
                if net not in circuit_graph:
                    if net in inout_ports:
                        circuit_graph.add_node(net,inst_type="net", net_type="external")
                    else:
                        circuit_graph.add_node(net,inst_type="net", net_type="internal")
                if "edge_weight" in node.keys():
                    #print("setting weight")
                    wt = node["edge_weight"][wt_index]
                else:
                    #print("setting weight as power")
                    wt = 2^wt_index
                    
                circuit_graph.add_edge(node["inst"], net,weight=wt)
                wt_index +=1
        #for node,attr in circuit_graph.nodes(data=True):
        #    print(attr)
        return circuit_graph
    def _laplacian_matrix(self, graph):
        L = nx.laplacian_matrix(graph, nodelist=None, weight='weight')
        print(L)
    def _show_circuit_graph(self,filename, graph):
        for subgraph in nx.connected_component_subgraphs(graph):
            color_map = []
            X, Y = bipartite.sets(subgraph)
            pos = dict()
            pos.update( (n, (1, i)) for i, n in enumerate(X) ) # put nodes from X at x=1
            pos.update( (n, (2, i)) for i, n in enumerate(Y) ) # put nodes from Y at x=2
            #nx.draw(B, pos=pos)
            #plt.show()
            plt.figure(figsize=(4, 4))
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
                             with_labels=True,pos=pos,node_size = 1200)
            plt.title(filename,fontsize=20)
            #plt.savefig("path.png")
            #plt.show()
            if not os.path.exists("library_graphs"):
                os.mkdir("library_graphs")
            nx.write_yaml(subgraph,"library_graphs/"+filename+".yaml")

# %% library:


if __name__ == '__main__':
    dir = "./basic_library/"
    for file in os.listdir(dir):
        if file.endswith(".sp"):
            fp = os.path.join(dir, file)
            print(fp)
            sp = spiceParser(fp)
            sp.parser()
    print("Reading Library Successful")
