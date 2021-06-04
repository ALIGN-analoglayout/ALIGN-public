#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 10:38:14 2021

@author: kunal001
"""
from ..schema.hacks import HierDictNode
from align.schema.graph import Graph

import logging
logger = logging.getLogger(__name__)


class CreateDatabase:
    def __init__(self, ckt_parser, const_parse):
        self.hier_graph_dict = {}
        self.const_parse = const_parse
        self.ckt_parser = ckt_parser

    def read_inputs(self, name: str):
        """
        read circuit graphs
        """
        G=Graph(self.ckt_parser.library.find(name))
        # self.ckt_parser.library.find(name)
        # top_ports = []
        ports_weight = {}
        for port in self.ckt_parser.library.find(name).pins:
            # # if 'source' in attr['inst_type']:
            # #     for source_nets in self.G.neighbors(node):
            # #         top_ports.append(source_nets)
            # if 'net_type' in attr:
            #     if attr['net_type'] == "external":
            #         top_ports.append(node)
            ports_weight[port] = []
            for nbr in list(G.neighbors(port)):
                pin = G.get_edge_data(nbr,port)["pin"]
                wt=[2**i for i,p in enumerate(['D', 'G', 'S', 'B']) if p in pin]
                ports_weight[port].append(wt)

        logger.debug("Merging nested graph hierarchies to dictionary: ")
        self.hier_graph_dict[name] = HierDictNode(
            name=name,
            graph=G,
            ports=self.ckt_parser.library.find(name).pins,
            ports_weight=ports_weight,
            constraints=[]
        )
        self.const_parse.annotate_user_constraints(self.hier_graph_dict[name])
        self._traverse_hier_in_graph(G)
        logger.debug(f"read graph {self.hier_graph_dict}")
        return self.hier_graph_dict

    def _traverse_hier_in_graph(self, G):
        """
        Recusively reads all hierachies in the graph and convert them to dictionary
        """
        for node, attr in G.nodes(data=True):
            if "sub_graph" in attr and attr["sub_graph"]:
                logger.debug(
                    f'Traversing sub graph: {node} {attr["inst_type"]} {attr["ports"]}')
                sub_ports = []
                ports_weight = {}
                for sub_node, sub_attr in attr["sub_graph"].nodes(data=True):
                    if 'net_type' in sub_attr:
                        if sub_attr['net_type'] == "external":
                            sub_ports.append(sub_node)
                            ports_weight[sub_node] = []
                            for nbr in list(attr["sub_graph"].neighbors(sub_node)):
                                ports_weight[sub_node].append(
                                    attr["sub_graph"].get_edge_data(sub_node, nbr)['weight'])

                logger.debug(
                    f'external ports: {sub_ports}, {attr["connection"]}, {ports_weight}')
                self.hier_graph_dict[attr["inst_type"]] = HierDictNode(
                    name=attr["inst_type"],
                    graph=attr["sub_graph"],
                    ports=sub_ports,
                    constraints=[],
                    ports_weight=ports_weight
                )
                self.const_parse.annotate_user_constraints(
                    self.hier_graph_dict[attr["inst_type"]])

                self._traverse_hier_in_graph(attr["sub_graph"])
