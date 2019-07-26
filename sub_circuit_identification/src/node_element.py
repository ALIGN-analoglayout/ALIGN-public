# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 14:53:57 2018

@author: kunal
"""

import networkx as nx
import matplotlib.pyplot as plt
import itertools as it
from collections import defaultdict


class advancedNode:
    """
    combines multiple nodes and return properties of new node.

    Parameters of input
    ----------
    nodes : all nodes with nodes names and properties
    ports : ports visible to outside the node

    Returns
    -------
    _no_of_ports : number
    _no_of_nodes : number

    Example
    -------
    >>> subckt = {"node_type": name, "ports": ports, "nodes": nodes}
    >>> advancedNode(subckt) 

    """

    def __init__(self, subckt):
        self.ports = subckt["ports"]
        self.nodes = subckt["nodes"]
        self.nets = defaultdict(list)
        self.node_graph = nx.Graph()
        self.inst_type = subckt["inst_type"]

    def _no_of_ports(self):
        return len(self.ports)

    def _no_of_nodes(self):
        return len(self.nodes)

    def _node_graph(self):
        for node in self.nodes:
            self.node_graph.add_node(node["inst"],
                                     inst_type=node["inst_type"],
                                     ports=node["ports"],
                                     values=node['values'])
            for net in node["ports"]:
                self.nets[net].append(node["inst"])
        for net, nodes in self.nets.items():
            if net not in ["0", "vdd!", "gnd!"]:
                for pair in it.combinations(nodes, 2):
                    self.node_graph.add_edge(*pair, name=net)

    def _match_graph(self):
        if self.inst_type is None:
            self.inst_type = "current mirror"
        else:
            pass

    def _show_circuit_graph(self):
        color_map = []
        plt.figure()
        for x, y in self.node_graph.nodes(data=True):
            if "inst_type" in y:
                if y["inst_type"] == 'pmos':
                    color_map.append('red')
                elif y["inst_type"] == 'nmos':
                    color_map.append('blue')
                elif y["inst_type"] == 'cap':
                    color_map.append('orange')
                else:
                    color_map.append('green')
        nx.draw_networkx(self.node_graph,
                         node_color=color_map,
                         with_labels=True)
        plt.title('node graph')

    def get_node(self):
        self._node_graph()
        self._match_graph()
        self._show_circuit_graph()
        return {
            'inst': subckt['inst'],
            'inst_type': self.inst_type,
            'ports': self.ports,
            'node_graph': self.node_graph
        }


name = "current_mirror"
nodes = [{
    'inst': 'M3',
    'inst_type': 'nmos',
    'ports': ['net7', 'net5', '0', '0'],
    'values': ['w=w', 'l=90n']
}, {
    'inst': 'M4',
    'inst_type': 'nmos',
    'ports': ['net5', 'net5', '0', '0'],
    'values': ['w=w', 'l=90n']
}]
ports = ['net7', 'net5', '0']
subckt = {'inst': "x0", "inst_type": name, "ports": ports, "nodes": nodes}
x1 = advancedNode(subckt)
new_node = x1.get_node()
print(new_node)
