# -*- coding: utf-8 -*-
"""
Created on Wed July 08 13:12:15 2020

@author: kunal
"""

from align.schema.graph import Graph
from collections import Counter
from itertools import combinations
from align.schema import SubCircuit, Instance
from .util import compare_two_nodes
from ..schema.types import set_context

import logging

logger = logging.getLogger(__name__)


def create_new_hiearchy(dl, parent_name, child_name, elements, pins_map=None):
    parent = dl.find(parent_name)
    # Create a subckt and add to library
    if not pins_map:
        pins_map = {}
        G = Graph(parent)
        for ele in elements:
            if G._is_element(ele):
                pins_map.update({net:net for net in G.neighbors(ele)})
        pins_map = { net:net for net in pins_map.keys()
            if not (net in parent.pins) and
            not (set(G.neighbors(net))-set(elements))
            }
    with set_context(dl):
        child = SubCircuit(child_name, pins=pins_map.keys())
        dl.append(child)
    # Add all instances of groupblock to new subckt
    pes = list()
    with set_context(child.elements):
        for ele in elements:
            pe = parent.get_element(ele)
            if pe:
                pes.append(pe)
                child.elements.append(pe)
    # Remove elements from subckt then add new_subckt instance
    inst_name = "X_"+child_name
    with set_context(parent.elements):
        for pe in pes:
            parent.elements.remove(pe)
        X1 = Instance(
            name=inst_name,
            model=child_name,
            pins=pins_map,
            generator=child_name,
        )
        parent.elements.append(X1)

class array_hierarchy:
    """
    Improves placement for circuits with arrays such as DAC, ADC, equalizer
    Creates a hierarchy for repeated elements
    """

    def __init__(self, dl, ckt, design_setup):
        """
        Args:
            ckt_data (dict): all subckt graph, names and port
            design_setup (dict): information from setup file
            library (list): list of library elements in dict format
            existing_generator (list): list of names of existing generators
        """
        self.dl = dl
        self.ckt = ckt
        self.graph = Graph(ckt)
        assert not ckt.name in design_setup['DIGITAL']
        assert design_setup["IDENTIFY_ARRAY"]==True
        self.pg = design_setup["POWER"] + design_setup["GND"]
        self.clk = design_setup["CLOCK"]
        self.stop_points = self.pg + self.clk

    def find_array(self, node: str, traversed: list):
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
        lvl1 = list(set(self.graph.neighbors(node)) - set(traversed))
        node_hier[node] = self.matching_groups(lvl1, None)
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
                        self.graph, similar_node_groups, visited, templates[node], array
                    )
                    logger.debug(f"similar groups final from {node}:{array}")

            # check number of lvls in detected array
            # single hierarchy arrays can be handled using simple approaches
            all_inst = []
            if array and len(array.values()) > 1 and len(list(array.values())[0]) > 1:
                # Multiple hierarchy identified in array
                for branch in array.values():
                    for node_hier in branch:
                        if (
                            self.graph.nodes[node_hier]["inst_type"] != "net"
                            and node_hier not in all_inst
                            and not self.graph.nodes[node_hier]["inst_type"]
                            .lower()
                            .startswith("cap")
                        ):
                            all_inst.append(node_hier)

            else:
                node_hier[node] = []
                for inst in array.keys():
                    if self.graph.nodes[inst]["inst_type"] != "net":
                        node_hier[node].append(inst)
            if len(all_inst) > 1:
                all_inst = sorted(all_inst)
                # TODO rewrite this code and tests
                create_new_hiearchy(self.dl, self.ckt.name, "array_hier_" + node, all_inst)

    def matching_groups(self, lvl1: list):
        similar_groups = []
        logger.debug(f"creating groups for all neighbors: {lvl1}")
        # TODO: modify this best case complexity from n*(n-1) to n complexity
        for l1_node1, l1_node2 in combinations(lvl1, 2):
            if compare_two_nodes(self.graph, l1_node1, l1_node2):
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

    def trace_template(self, similar_node_groups, visited, template, array):
        next_match = {}
        traversed = visited.copy()

        for source, groups in similar_node_groups.items():
            next_match[source] = []
            for node in groups:
                lvl1 = list(set(self.graph.neighbors(node)) - set(traversed))
                next_match[source] += lvl1
                visited += lvl1
            if len(next_match[source]) == 0:
                del next_match[source]

        if len(next_match.keys()) > 0 and self.match_branches(next_match):
            for source in array.keys():
                if source in next_match.keys():
                    array[source] += next_match[source]

            template += next_match[list(next_match.keys())[0]]
            logger.debug(
                f"found matching lvl {template}, {similar_node_groups}, {visited}"
            )
            if self.check_convergence(next_match):
                self.trace_template(next_match, visited, template, array)

    def match_branches(self, nodes_dict):
        logger.debug(f"matching next lvl branches {nodes_dict}")
        nbr_values = {}
        for node, nbrs in nodes_dict.items():
            # super_dict={}
            super_list = []
            if len(nbrs) == 1:
                return False
            for nbr in nbrs:
                if self.graph.nodes[nbr]["inst_type"] == "net":
                    super_list.append("net")
                    super_list.append(self.graph.nodes[nbr]["net_type"])
                else:
                    super_list.append(self.graph.nodes[nbr]["inst_type"])
                    for v in self.graph.nodes[nbr]["values"].values():
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
