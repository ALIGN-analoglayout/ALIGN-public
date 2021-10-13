# -*- coding: utf-8 -*-
"""
Created on Wed July 08 13:12:15 2020

@author: kunal
"""

from collections import Counter
from itertools import combinations

from .util import compare_two_nodes
from ..schema import constraint
from ..schema.hacks import HierDictNode

import logging

logger = logging.getLogger(__name__)


class array_hierarchy:
    """
    Improves placement for circuits with arrays such as DAC, ADC, equalizer
    Creates a hierarchy for repeated elements
    """

    def __init__(self, ckt_data, design_setup, library, existing_generator):
        """
        Args:
            ckt_data (dict): all subckt graph, names and port
            design_setup (dict): information from setup file
            library (list): list of library elements in dict format
            existing_generator (list): list of names of existing generators
        """
        self.ckt_data = ckt_data
        self.digital = design_setup["DIGITAL"]
        self.pg = design_setup["POWER"] + design_setup["GND"]
        self.lib = library
        self.clk = design_setup["CLOCK"]
        self.all_lef = existing_generator
        self.stop_points = self.pg + self.clk
        self.identify_array = design_setup["IDENTIFY_ARRAY"]
        self.lib_names = [lib_ele.name for lib_ele in library]

    def create_hierarchy(self, graph, node: str, traversed: list):
        """
        Creates array hierarchies starting from input node

        Parameters
        ----------
        graph : TYPE
            DESCRIPTION.
        node : str
            node with high fanout.
        traversed : list
            DESCRIPTION.
        Returns
        -------
        node_hier : TYPE
            DESCRIPTION.

        """
        node_hier = {}
        lvl1 = list(set(graph.neighbors(node)) - set(traversed))
        node_hier[node] = self.matching_groups(graph, lvl1, None)
        logger.debug(f"new hierarchy points {node_hier} from node {node}")

        if len(node_hier[node]) > 0:
            for group in sorted(node_hier[node], key=lambda group: len(group)):
                if len(group) > 0:
                    templates = {}
                    similar_node_groups = {}
                    for el in sorted(group):
                        similar_node_groups[el] = [el]
                    templates[node] = [el]
                    visited = group
                    array = similar_node_groups.copy()
                    self.trace_template(
                        graph, similar_node_groups, visited, templates[node], array
                    )
                    logger.debug(f"similar groups final from {node}:{array}")

            # check number of lvls in detected array
            # single hierarchy arrays can be handled using simple approaches
            all_inst = []
            if array and len(array.values()) > 1 and len(list(array.values())[0]) > 1:
                # Multiple hierarchy identified in array
                matched_ports = {}
                for branch in array.values():
                    for node_hier in branch:
                        if (
                            graph.nodes[node_hier]["inst_type"] != "net"
                            and node_hier not in all_inst
                            and not graph.nodes[node_hier]["inst_type"]
                            .lower()
                            .startswith("cap")
                        ):
                            all_inst.append(node_hier)

            else:
                node_hier[node] = []
                for inst in array.keys():
                    if graph.nodes[inst]["inst_type"] != "net":
                        node_hier[node].append(inst)
            if len(all_inst) > 1:
                all_inst = sorted(all_inst)
                h_ports_weight = {}
                for inst in all_inst:
                    for node_hier in list(set(graph.neighbors(inst))):
                        if graph.nodes[node_hier]["inst_type"] == "net":
                            if (
                                set(graph.neighbors(node_hier)) - set(all_inst)
                            ) or graph.nodes[node_hier]["net_type"] == "external":
                                matched_ports[node_hier] = node_hier
                                h_ports_weight[node_hier] = []
                                for nbr in list(graph.neighbors(node_hier)):
                                    h_ports_weight[node_hier].append(
                                        graph.get_edge_data(node_hier, nbr)["weight"]
                                    )

                logger.debug(
                    f"creating a new hierarchy for {node}, {all_inst}, {matched_ports}"
                )
                # subgraph,_ = merge_nodes(graph, 'array_hier_'+node,all_inst , matched_ports)
                subgraph = None
                # TODO rewrite this code and tests
                node_hier[node] = HierDictNode(
                    name="array_hier_" + node,
                    graph=subgraph,
                    ports=list(matched_ports.keys()),
                    ports_match=matched_ports,
                    ports_weight=h_ports_weight,
                    constraints=[],
                    size=len(subgraph.nodes()),
                )
            return node_hier

    def matching_groups(self, G, lvl1: list, ports_weight):
        """
        Creates a a 2D list from 1D list of lvl1, grouping similar elements in separate group

        Parameters
        ----------
        G : TYPE
            DESCRIPTION.
        lvl1 : TYPE
            DESCRIPTION.
        ports_weight : TYPE
            DESCRIPTION.
        Returns
        -------
        similar_groups : TYPE
            DESCRIPTION.

        """

        similar_groups = []
        logger.debug(f"creating groups for all neighbors: {lvl1}")
        # modify this best case complexity from n*(n-1) to n complexity
        for l1_node1, l1_node2 in combinations(lvl1, 2):
            if compare_two_nodes(G, l1_node1, l1_node2, ports_weight):
                found_flag = 0
                logger.debug("similar_group %s", similar_groups)
                for index, sublist in enumerate(similar_groups):
                    if l1_node1 in sublist and l1_node2 in sublist:
                        found_flag = 1
                        break
                    if l1_node1 in sublist:
                        similar_groups[index].append(l1_node2)
                        found_flag = 1
                        break
                    elif l1_node2 in sublist:
                        similar_groups[index].append(l1_node1)
                        found_flag = 1
                        break
                if found_flag == 0:
                    similar_groups.append([l1_node1, l1_node2])
        return similar_groups

    def trace_template(self, graph, similar_node_groups, visited, template, array):
        next_match = {}
        traversed = visited.copy()

        for source, groups in similar_node_groups.items():
            next_match[source] = []
            for node in groups:
                lvl1 = list(set(graph.neighbors(node)) - set(traversed))
                next_match[source] += lvl1
                visited += lvl1
            if len(next_match[source]) == 0:
                del next_match[source]

        if len(next_match.keys()) > 0 and self.match_branches(graph, next_match):
            for source in array.keys():
                if source in next_match.keys():
                    array[source] += next_match[source]

            template += next_match[list(next_match.keys())[0]]
            logger.debug(
                "found matching lvl: %s,%s,%s", template, similar_node_groups, visited
            )
            if self.check_convergence(next_match):
                self.trace_template(graph, next_match, visited, template, array)

    def match_branches(self, graph, nodes_dict):
        logger.debug(f"matching next lvl branches {nodes_dict}")
        nbr_values = {}
        for node, nbrs in nodes_dict.items():
            # super_dict={}
            super_list = []
            if len(nbrs) == 1:
                return False
            for nbr in nbrs:
                if graph.nodes[nbr]["inst_type"] == "net":
                    super_list.append("net")
                    super_list.append(graph.nodes[nbr]["net_type"])
                else:
                    super_list.append(graph.nodes[nbr]["inst_type"])
                    for v in graph.nodes[nbr]["values"].values():
                        super_list.append(v)
            nbr_values[node] = Counter(super_list)
        _, main = nbr_values.popitem()
        for node, val in nbr_values.items():
            if val == main:
                continue
            else:
                return False
        return True

    def check_convergence(self, match: dict):
        vals = []
        for val in match.values():
            if set(val).intersection(vals):
                return False
            else:
                vals += val
