#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 10:38:14 2021

@author: kunal001
"""
import logging
logger = logging.getLogger(__name__)

class CreateDatabase:
    def __init__(self,hier_graph,const_parse):
        self.hier_graph_dict = {}
        self.const_parse = const_parse
        self.G = hier_graph
        
    def read_inputs(self,name:str):
        """
        read circuit graphs
        """
        top_ports = []
        ports_weight = {}
        for node, attr in self.G.nodes(data=True):
            if 'source' in attr['inst_type']:
                for source_nets in self.G.neighbors(node):
                    top_ports.append(source_nets)
            elif 'net_type' in attr:
                if attr['net_type'] == "external":
                    top_ports.append(node)
                    ports_weight[node]=[]
                    for nbr in list(self.G.neighbors(node)):
                        ports_weight[node].append(self.G.get_edge_data(node, nbr)['weight'])
    
        logger.debug("Merging nested graph hierarchies to dictionary: ")
        const = self.const_parse.read_user_const(name)
        self.hier_graph_dict[name] = {
            "graph": self.G,
            "ports": top_ports,
            "ports_weight": ports_weight,
            "const": const
        }
        
        self._traverse_hier_in_graph(self.G)
        logger.debug(f"read graph {self.hier_graph_dict}")
        return self.hier_graph_dict
    
    def _traverse_hier_in_graph(self,G):
        """
        Recusively reads all hierachies in the graph and convert them to dictionary
        """
        for node, attr in G.nodes(data=True):
            if "sub_graph" in attr and attr["sub_graph"]:
                logger.debug(f'Traversing sub graph: {node} {attr["inst_type"]} {attr["ports"]}')
                sub_ports = []
                ports_weight = {}
                for sub_node, sub_attr in attr["sub_graph"].nodes(data=True):
                    if 'net_type' in sub_attr:
                        if sub_attr['net_type'] == "external":
                            sub_ports.append(sub_node)
                            ports_weight[sub_node] = []
                            for nbr in list(attr["sub_graph"].neighbors(sub_node)):
                                ports_weight[sub_node].append(attr["sub_graph"].get_edge_data(sub_node, nbr)['weight'])
    
                logger.debug(f'external ports: {sub_ports}, {attr["connection"]}, {ports_weight}')
                const = self.const_parse.read_user_const(attr["inst_type"])
    
                self.hier_graph_dict[attr["inst_type"]] = {
                    "graph": attr["sub_graph"],
                    "ports": sub_ports,
                    "const": const,
                    "ports_weight": ports_weight
                }
    
                self._traverse_hier_in_graph(attr["sub_graph"])
                