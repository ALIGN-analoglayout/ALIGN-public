# -*- coding: utf-8 -*-
"""
Created on Wed July 08 13:12:15 2020

@author: kunal
"""

from align.schema.graph import Graph
from collections import Counter
from itertools import combinations
from align.schema import SubCircuit, Instance
from .util import compare_two_nodes, reduced_SD_neighbors
from ..schema.types import set_context
from ..schema import constraint

import pprint
import logging

logger = logging.getLogger(__name__)


class process_arrays:
    """
    Improves placement for circuits with arrays such as DAC, ADC, equalizer
    Creates a hierarchy for repeated elements
    """

    def __init__(self, ckt, match_pairs):
        """
        Args:
            ckt_data (dict): all subckt graph, names and port
            design_setup (dict): information from setup file
            library (list): list of library elements in dict format
            existing_generator (list): list of names of existing generators
        """
        self.dl = ckt.parent
        self.ckt = ckt
        self.graph = Graph(ckt)
        self.stop_points = list()
        self.condition = True
        self.is_digital = False
        for const in ckt.constraints:
            if isinstance(const, constraint.PowerPorts) or\
                isinstance(const, constraint.GroundPorts) or \
                isinstance(const, constraint.ClockPorts):
                self.stop_points.extend(const.ports)
            elif isinstance(const, constraint.IdentifyArray):
                self.condition = const.isTrue
            elif isinstance(const, constraint.IsDigital):
                self.is_digital = const.isTrue
        self.match_pairs = {k: v for k, v in match_pairs.items() if len(v) > 1}
        self.name = ckt.name
        self.iconst = ckt.constraints
        self.hier_sp = set()
        self.align_block_const = dict()
        self.new_hier_instances = dict()
        self._filter_start_points_from_match_pairs()
        self._check_array_start_points(self.stop_points)

    def _filter_start_points_from_match_pairs(self):
        for k, pair in self.match_pairs.items():
            logger.debug(f"all pairs from {k}:{pair}")
            if "start_point" in pair.keys():
                if pair["start_point"] and isinstance(pair["start_point"][0], str):
                    # Check later for CTDTDSM
                    self.hier_sp.update(pair["start_point"])
                del pair["start_point"]
                logger.debug(f"New symmetrical start points {pair}")
        logger.debug(f"updated match pairs: {pprint.pformat(self.match_pairs, indent=4)}")

    def _check_array_start_points(self, traversed):
        logger.debug(f"new hier start points: {self.hier_sp}")
        for sp in sorted(self.hier_sp):
            logger.debug(
                f"Searching arrays from:{sp}\
                traversed: {traversed} \
                existing match pairs: {pprint.pformat(self.match_pairs, indent=4)}"
            )
            if sp not in self.graph.nodes():
                logger.debug(f"{sp} not found in graph {self.graph.nodes()}")
                continue
            array = self.find_array(sp, traversed)
            if array:
                logger.debug(f"found array instances {array}")
        logger.debug(f"updated match pairs: {pprint.pformat(self.match_pairs, indent=4)}")

    def find_array(self, start_node: str, traversed: list):
        """
        Creates array hierarchies starting from input node

        Parameters
        ----------
        node : str
            node with high fanout.
        traversed : list
            DESCRIPTION.
        """
        if not self.condition:
            logger.info(f"auto-array generation set to false")
            return
        elif self.is_digital:
            logger.info(f'cant identify array in digital ckt {self.name}')
            return

        node_hier = {}
        lvl1 = list(set(self.graph.neighbors(start_node)) - set(traversed))
        node_hier[start_node] = self.matching_groups(start_node, lvl1)
        logger.debug(f"new hierarchy points {node_hier} from {start_node}")
        if len(node_hier[start_node]) == 0:
            return
        for group in sorted(node_hier[start_node], key=lambda group: len(group)):
            if len(group) > 0:
                templates = {}
                match_grps = {}
                for el in sorted(group):
                    match_grps[el] = [el]
                templates[start_node] = list()
                visited = group + self.stop_points + [el] + [start_node]
                array = match_grps.copy()
                self.trace_template(match_grps, visited, templates[start_node], array)
                logger.debug(f"similar groups final from {start_node}:{array}")
        # converts results to a 2D/1D list
        return self.process_results(start_node, array)

    def process_results(self, start_node, array):
        if not array:
            logger.debug(f"no symmetry from {start_node}")
            return
        array_2D = list()
        for inst_list in array.values():
            array_2D.append([inst for inst in inst_list \
                if self.ckt.get_element(inst)])
        if len(array_2D[0])==1:
            self.align_block_const[start_node] = [inst[0] for inst in array_2D]
            return self.align_block_const[start_node]
        else:
            self.new_hier_instances[start_node] = array_2D
            return array_2D

    def matching_groups(self, node, lvl1: list):
        similar_groups = list()
        logger.debug(f"creating groups for all neighbors: {lvl1}")
        # TODO: modify this best case complexity from n*(n-1) to n complexity
        for l1_node1, l1_node2 in combinations(lvl1, 2):
            if compare_two_nodes(self.graph, l1_node1, l1_node2) and \
                self.graph.get_edge_data(node, l1_node1)['pin'] == \
                self.graph.get_edge_data(node, l1_node2)['pin']:
                found_flag = 0
                logger.debug(f"similar groups {similar_groups}")
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

    def trace_template(self, match_grps, visited, template, array):
        next_match = {}
        traversed = visited.copy()
        logger.debug(f"tracing groups {match_grps} visited {visited}")
        for source, groups in match_grps.items():
            next_match[source] = list()
            for node in groups:
                nbrs = set(self.graph.neighbors(node)) - set(traversed)
                lvl1 = [nbr for nbr in nbrs if reduced_SD_neighbors(self.graph, node, nbr)]
                # logger.debug(f"lvl1 {lvl1} {set(self.graph.neighbors(node))} {traversed}")
                next_match[source].extend(lvl1)
                visited += lvl1
            if not next_match[source]:
                del next_match[source]

        if next_match and self.match_branches(next_match):
            for source in array.keys():
                if source in next_match.keys():
                    array[source] += next_match[source]

            template += next_match[list(next_match.keys())[0]]
            logger.debug(f"found matching lvl {template}, {match_grps}")
            if self.check_non_convergence(next_match):
                self.trace_template(next_match, visited, template, array)

    def match_branches(self, nodes_dict):
        logger.debug(f"matching next lvl branches {nodes_dict} stop points: {self.stop_points}")
        nbr_values = {}
        for node, nbrs in nodes_dict.items():
            super_list = list()
            for nbr in nbrs:
                if self.graph._is_element(self.graph.nodes[nbr]):
                    inst = self.graph.element(nbr)
                    # logger.debug(f"instance {inst}")
                    # super_list.append(inst.model)
                    super_list.append(inst.abstract_name)
                else:
                    super_list.append("net")
            logger.debug(f"all probable neighbors from {node} {super_list}")
            nbr_values[node] = Counter(super_list)
        logger.debug(f"all nbr properties {nbr_values}")
        _, main = nbr_values.popitem()
        for node, val in nbr_values.items():
            if val == main:
                continue
            else:
                return False
        return True

    def check_non_convergence(self, match: dict):
        vals = list()
        for val in match.values():
            common_node = set(val).intersection(vals)
            common_element = [node for node in common_node if self.graph._is_element(node)]
            if common_element:
                logger.debug(f"{common_element} already existing , ending further array search")
                return False
            else:
                vals += val
        logger.debug("not converging level")
        return True

    def add_align_block_const(self):
        logger.debug(f"AlignBlock const: {self.align_block_const}")
        for key, inst_list in self.align_block_const.items():
            logger.debug(f"align instances: {inst_list}")
            h_blocks = [inst for inst in inst_list \
                if inst in self.graph]
            if len(h_blocks) > 0:
                with set_context(self.iconst):
                    self.iconst.append(constraint.Align(line="h_center", instances=h_blocks))
            # del self.match_pairs[key]
        logger.debug(f"AlignBlock const update {self.iconst}")
        # hier_keys = [key for key, value in self.match_pairs.items() if "name" in value.keys()]
        # for key in hier_keys:
        #     del self.match_pairs[key]
        # return hier_keys

    def add_new_array_hier(self):
        logger.debug(f"New hierarchy instances: {self.new_hier_instances}")
        sub_hier_elements = set()
        for key, array_2D in self.new_hier_instances.items():
            logger.debug(f"new hier instances: {array_2D}")
            all_inst = [inst for template in array_2D for inst in template
                if inst in self.graph and inst not in sub_hier_elements]
            #Filter repeated elements across array of obejcts
            repeated_elements = set([inst for inst, count in Counter(all_inst).items() if count>1])
            all_inst = set(all_inst) - repeated_elements
            array_2D = [list(set(array_1D) - repeated_elements) for array_1D in array_2D]
            sub_hier_elements.update(all_inst)
            if len(all_inst) <=1:
                logger.debug(f"not enough elements to create a hierarchy")
                continue
            new_array_hier_name = "ARRAY_HIER_" + key
            create_new_hiearchy(self.dl, self.name, new_array_hier_name, all_inst)
            all_template_names = list()
            for template in array_2D:
                template_name = self.get_new_subckt_name("ARRAY_TEMPLATE")
                create_new_hiearchy(self.dl, new_array_hier_name, template_name, template)
                all_template_names.append(template_name)
            self.add_array_placement_constraints(new_array_hier_name, all_template_names)

    def add_array_placement_constraints(self, hier, modules):
        #TODO make it sizing aware
        # array placement constraint
        arre_hier_const = self.dl.find(hier).constraints
        with set_context(arre_hier_const):
            instances = ['X_'+module for module in modules]
            arre_hier_const.append(constraint.Align(line="h_center", instances=instances))
            arre_hier_const.append(constraint.SameTemplate(instances=instances))
        # template placement constraint
        # for template in modules:
        #     template_module = self.dl.find(template)
        #     all_inst = [inst.name for inst in template_module.elements]
        #     with set_context(template_module.constraints):
        #         template_module.constraints.append(constraint.Align(line="v_center", instances=all_inst))


    def get_new_subckt_name(self, name):
        count =1
        new_name = name
        while self.ckt.parent.find(new_name):
            new_name = name + str(count)
            count +=1
        return new_name

def create_new_hiearchy(dl, parent_name, child_name, elements, pins_map=None):
    parent = dl.find(parent_name)
    # Create a subckt and add to library
    logger.info(f"adding new array hierarchy {child_name} elements {elements}")
    if not pins_map:
        pins_map = {}
        G = Graph(parent)
        logger.debug(f"{parent.elements}")
        for ele in elements:
            if parent.get_element(ele):
                pins_map.update({net:net for net in G.neighbors(ele)})
        logger.debug(f"pins {pins_map} {elements} {parent.pins}")
        pins_map = { net:net for net in pins_map.keys()
            if net in parent.pins or
             (set(G.neighbors(net))-set(elements))
            }
    if not pins_map:
        logger.error(f"can't create module with no pins")
        return
    logger.debug(f"new subckt pins : {pins_map}")
    assert not dl.find(child_name), f"subcircuit {child_name} already existing"
    with set_context(dl):
        logger.debug(pins_map.keys)
        child = SubCircuit(name=child_name, pins=list(pins_map.keys()))
        dl.append(child)
    # Add all instances of groupblock to new subckt
    pes = list()
    with set_context(child.elements):
        for ele in elements:
            pe = parent.get_element(ele)
            if pe:
                pes.append(pe)
                child.elements.append(pe)
    # Transfer global constraints
    with set_context(child.constraints):
        for const in list(parent.constraints):
            if any(
                isinstance(const, x)
                for x in [
                    constraint.HorizontalDistance,
                    constraint.VerticalDistance,
                    constraint.BlockDistance,
                    constraint.CompactPlacement,
                ]
            ):
                child.constraints.append(const)
    # Remove elements from subckt then add new_subckt instance
    inst_name = "X_"+child_name
    with set_context(parent.elements):
        for pe in pes:
            parent.elements.remove(pe)
        X1 = Instance(
            name=inst_name,
            model=child_name,
            pins=pins_map,
            abstract_name = child_name
        )
        parent.elements.append(X1)