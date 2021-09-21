# -*- coding: utf-8 -*-
"""
Created on Wed Feb 21 13:12:15 2020

@author: kunal
"""

from typing import List
from align.schema.types import set_context
import pprint
from itertools import combinations, combinations_with_replacement
import logging

from .create_array_hierarchy import array_hierarchy
from .util import compare_two_nodes, get_base_model, reduced_neighbors, reduced_SD_neighbors, get_leaf_connection
from ..schema import constraint
from ..schema.graph import Graph
from align.schema.subcircuit import SubCircuit

logger = logging.getLogger(__name__)

def find_unique_matching_branches(G, nbrs1, nbrs2, ports_weight):
    logger.debug(f"finding unique matches between {nbrs1},{nbrs2}")
    match = {}
    for node1 in nbrs1:
        for node2 in nbrs2:
            if compare_two_nodes(G, node1, node2, ports_weight):
                if node1 in match:
                    return False
                else:
                    match[node1] = node2
        if node1 not in match:
            return False
    return match

def compare_nodes(G, match_pairs, match_pair, traversed, node1, node2, ports_weight):
    """
    Traversing single branch for symmetry
    condition 1, Single branch: both ports/ nets are same and connected to two or more ports
    condition 2, Converging branch: two nets are diffrent but connected to single device node
    condition 3: Two parallel branches
    condition 3: Two branches with multiple fanout will create new start points
    condition 4: Diverging branch with more than 2 fanout, check all pairs

    Parameters
    ----------
    G : networkx graph
        reduced hierarchical circuit graph.
    match_pair : dict type
        stores list of matched pairs.
    traversed : list of nodes already traversed, to avoid retracing
    node1,node2 : start points to create trees for comparison
    ports_weight :TYPE. dict
        dictionary of port weights
    Returns
    -------
    match_pair : dict type
        stores list of matched pairs.

    """
    logger.debug(f"comparing {node1}, {node2}, traversed {traversed}")
    nbrs1 = sorted(set(G.neighbors(node1)) - set(traversed))
    # remove dummies get_leaf_connection(subckt, port)

    nbrs1 = sorted(set([nbr for nbr in nbrs1 if reduced_neighbors(G, node1, nbr)]))
    nbrs2 = sorted(set(G.neighbors(node2)) - set(traversed))
    # remove dummies
    nbrs2 = sorted(set([nbr for nbr in nbrs2 if reduced_neighbors(G, node2, nbr)]))
    logger.debug(f"node1:{node1},property: {G.nodes[node1]},neigbors1: {nbrs1}")
    logger.debug(f"node2:{node2},property: {G.nodes[node2]},neigbors2: {nbrs2}")
    if not nbrs1 or not nbrs2:
        if compare_two_nodes(G, node1, node2, ports_weight):
            match_pair[node1] = node2
        logger.debug(f"no new neighbours, returning recursion {match_pair}")
        return
    elif len(nbrs1) > 10:
        if "start_point" in match_pair.keys():
            match_pair["start_point"] += [node1, node2]
        else:
            match_pair["start_point"] = [node1, node2]
        logger.debug(f"skipping high fanout nets{node1, nbrs1}")
        traversed.append(node1)
        return

    if node1 == node2:
        if node1 in match_pair.keys() or node1 in match_pair.values():
            logger.debug("avoid existing pair wise symmetry")
            return
        logger.debug(f"single node {node1}, nbrs {nbrs1}, nbr_weight {[G.get_edge_data(node1,nbr) for nbr in nbrs1]}")
        SD_nbrs = [nbr for nbr in nbrs1 if reduced_SD_neighbors(G, node1, nbr)]
        ## TBD: filter based on primitive constraints
        ## Right now will try to figure out S/D paths
        if len(SD_nbrs) == 0:
            logger.debug(f"No SD paths found to traverse")
            match_pair[node1] = node1
        elif len(SD_nbrs) == 1:
            logger.debug(f"traversing single S/D path {SD_nbrs}")
            match_pair[node1] = node1
            traversed.append(node1)
            compare_nodes(
                G,
                match_pairs,
                match_pair,
                traversed,
                SD_nbrs[0],
                SD_nbrs[0],
                ports_weight,
            )
        else:
            logger.debug(f"multiple nodes diverging {SD_nbrs}")
            logger.debug(f"nbr weights: {SD_nbrs} {[G.get_edge_data(node1, nbr)['pin'] for nbr in SD_nbrs]}")
            match_pair[node1] = node1
            traversed.append(node1)
            new_sp = sorted(set(SD_nbrs) - set(traversed))
            all_match_pairs_local = {}
            for nbr1, nbr2 in combinations(new_sp, 2):
                logger.debug(f"recursive pair call from single branch {nbr1} {nbr2}")
                new_pair = {}
                compare_nodes(
                    G,
                    match_pairs,
                    new_pair,
                    traversed.copy(),
                    nbr1,
                    nbr2,
                    ports_weight,
                )
                if new_pair:
                    # new_pair[nbr1]=nbr2
                    all_match_pairs_local[nbr1 + "_" + nbr2] = new_pair
            all_match_pairs_local = {
                k: v for k, v in all_match_pairs_local.items() if len(v) > 0
            }
            if len(all_match_pairs_local) == 1:
                match_pair.update(
                    all_match_pairs_local[list(all_match_pairs_local.keys())[0]]
                )
                logger.debug(
                    f"found inline pair: {pprint.pformat(match_pair, indent=4)}"
                )
            else:
                for nbr1 in new_sp:
                    if nbr1 + "_" + nbr1 not in match_pairs.keys():
                        logger.debug(
                            f"recursive single branch call from single branch {nbr1} {nbr1}"
                        )
                        new_pair = {}
                        compare_nodes(
                            G,
                            match_pairs,
                            new_pair,
                            traversed.copy(),
                            nbr1,
                            nbr1,
                            ports_weight,
                        )
                        # filtering multiple axis of symmetries with same block, ideally they should be handled by array generation
                        if new_pair:
                            match_pairs[nbr1 + "_" + nbr1] = new_pair
                            logger.debug(
                                f"updating match pairs: {pprint.pformat(match_pairs, indent=4)}"
                            )

    elif node1 == node2 and nbrs1 == nbrs2:
        logger.debug(f"traversing converging branch")
        match_pair[node1] = node2
        traversed += [node1, node2]
        nbrs1 = sorted(set(nbrs1) - set([node1, node2]))
        logger.debug(f"all non traversed neighbours: {nbrs1}")
        if len(nbrs1) == 1:
            nbr1 = nbr2 = nbrs1[0]
            logger.debug(f"keeping single converged branch inline {nbr1} {nbr2}")
            compare_nodes(G, match_pairs, match_pair, traversed.copy(), nbr1, nbr2, ports_weight)
        else:
            for nbr1, nbr2 in combinations_with_replacement(nbrs1, 2):
                logger.debug(f"recursive call from converged branch {nbr1} {nbr2}")
                if nbr1 + "_" + nbr2 not in match_pairs.keys():
                    new_pair = {}
                    compare_nodes(G, match_pairs, new_pair, traversed.copy(), nbr1, nbr2, ports_weight)
                    # filtering multiple axis of symmetries with same block, ideally they should be handled by array generation
                    if new_pair:
                        match_pairs[nbr1 + "_" + nbr2] = new_pair
                        logger.debug(f"updating match pairs: {pprint.pformat(match_pairs, indent=4)}")

    elif compare_two_nodes(G, node1, node2, ports_weight):
        nbrs1 = sorted(set([nbr for nbr in nbrs1 if G.get_edge_data(node1, nbr)["pin"] != {"B"}]))
        nbrs2 = sorted(set([nbr for nbr in nbrs2 if G.get_edge_data(node2, nbr)["pin"] != {"B"}]))
        match_pair[node1] = node2
        traversed += [node1, node2]
        logger.debug(f"Traversing parallel branches from {node1},{node2} {nbrs1}, {nbrs2}")
        nbrs1_wt = [pin for nbr in nbrs1 for pin in G.get_edge_data(node1, nbr)["pin"]]
        nbrs2_wt = [pin for nbr in nbrs2 for pin in G.get_edge_data(node2, nbr)["pin"]]
        logger.debug(f"nbr1 conn: {nbrs1_wt}, nbr2 {nbrs2_wt}")
        unique_match = find_unique_matching_branches(G, nbrs1, nbrs2, ports_weight)
        if len(nbrs1) == 0 or len(nbrs2) == 0:
            logger.debug(f"no new SD neihbours, returning recursion {match_pair}")
        elif len(nbrs1) == 1 and len(nbrs2) == 1:
            logger.debug(f"traversing binary branch")
            compare_nodes(G, match_pairs, match_pair, traversed, nbrs1.pop(), nbrs2.pop(), ports_weight)
        elif unique_match:
            logger.debug(f"traversing unique matches {unique_match}")
            match_pair[node1] = node2
            traversed += [node1, node2]
            for nbr1, nbr2 in unique_match.items():
                logger.debug(f"recursive call from pair {node1}:{node2} to {nbr1}:{nbr2}")
                compare_nodes(G, match_pairs, match_pair, traversed.copy(), nbr1, nbr2, ports_weight)
        elif (
            len(nbrs1_wt) > len(set(nbrs1_wt)) > 1
            and len(nbrs2_wt) > len(set(nbrs2_wt)) > 1
        ):
            logger.debug(f"setting new start points {node1} {node2}")
            match_pair[node1] = node2
            if "start_point" in match_pair.keys():
                match_pair["start_point"] += [node1, node2]
            else:
                match_pair["start_point"] = [node1, node2]
        else:
            match_pair = {}
            logger.debug(f"end all traversal from binary branch {node1} {node2}")
    else:
        match_pair = {}
        logger.debug(f"end of recursion branch, matches {match_pair}")


def recursive_start_points(G, match_pairs, traversed, node1, node2, ports_weight):
    logger.debug(f"Symmetry start point {node1} {node2}")
    pair = {}
    if node1 in G.nodes() and node2 in G.nodes():
        compare_nodes(G, match_pairs, pair, traversed, node1, node2, ports_weight)
    if not pair:
        logger.debug(f"No pair found from {node1} {node2}")
        return
    # TODO: use tuple instead of string
    match_pairs[node1 + node2] = pair
    logger.debug(f"updating match pairs (start): {pprint.pformat(match_pairs, indent=4)}")
    # Check for array start points
    hier_start_points = []
    for k, pair in match_pairs.items():
        logger.debug(f"all pairs from {k}:{pair}")
        if "start_point" in pair.keys():
            if pair["start_point"] and isinstance(pair["start_point"][0], str):
                # Check later for CTDTDSM
                hier_start_points.extend(pair["start_point"])
            del pair["start_point"]
            logger.debug(f"New symmetrical start points {pair}")
    logger.debug(f"updating match pairs: {pprint.pformat(match_pairs, indent=4)}")
    if not hier_start_points:
        return
    assert hier_start_points
    # TODO array hieararchy to be reimplemented
    return
    logger.debug(f"Creating new node from binary branch: {hier_start_points}")
    for sp in sorted(set(hier_start_points)):
        logger.debug(
            f"starting new node from binary branch:{sp} {hier_start_points} traversed {traversed} existing {pprint.pformat(match_pairs, indent=4)}"
        )
        if sp not in G.nodes():
            logger.debug(f"{sp} not found in graph {G.nodes()}")
            continue
        multifanout = array_hierarchy(G, sp, traversed, ports_weight)
        if multifanout and isinstance(multifanout[sp], list):
            logger.debug(
                f"only one level matched so putting as align block:{multifanout[sp]}"
            )
            match_pairs[node1 + node2 + "_align"] = {"start_point": multifanout[sp]}
        elif multifanout and isinstance(multifanout[sp], dict):
            logger.debug(
                f"more than one depth matched so creating new hierarchy :{multifanout[sp]}"
            )
            traversed += [node1, node2]
            match_pairs[sp + "_new_hier"] = multifanout[sp].copy()
            # for  h_port1, h_port2 in combinations(multifanout[sp]['ports'],2):
            #     recursive_start_points(multifanout[sp]['graph'],match_pairs,traversed.copy(),h_port1, h_port2, multifanout[sp]['ports_weight'])
        else:
            logger.debug(f"no symmetry from {sp}")
    logger.debug(
        f"updating match pairs end: {pprint.pformat(match_pairs, indent=4)}"
    )

def FindSymmetry(subckt, stop_points: list):
    """
    Find matching constraint starting from all port pairs.
    check: recursive_start_points
    Parameters
    ----------
    stop_points : list
        starts with power, ground and clock signals adds based on traversal.
    Returns
    -------
    None.

    """
    graph = Graph(subckt)
    ports = subckt.pins
    match_pairs = {}
    non_power_ports = sorted(set(sorted(ports)) - set(stop_points))
    logger.debug(f"subckt: {subckt.name} sorted signal ports: {non_power_ports}")
    ports_weight = {}
    for port in subckt.pins:
        leaf_conn = get_leaf_connection(subckt, port)
        logger.debug(f"leaf connections of net ({port}): {leaf_conn}")
        assert len(leaf_conn) > 0, f"floating port:{port} in subckt {subckt.name}"
        ports_weight[port] = set(sorted(leaf_conn))
    # TODO start from primitives
    for port1, port2 in combinations_with_replacement(non_power_ports, 2):
        traversed = stop_points.copy()
        if ports_weight[port1] == ports_weight[port2] and ports_weight[port2]:
            traversed += [port1, port2]
            recursive_start_points(graph, match_pairs, traversed, port1, port2, ports_weight)
            match_pairs = {k: v for k, v in match_pairs.items() if len(v) > 0}
            logger.debug(f"Matches starting from {port1, port2} pair: {pprint.pformat(match_pairs, indent=4)}")
    return match_pairs

def FindConst(ckt_data, name, stop_points=None):
    logger.debug(f"Searching constraints for block {name}")
    logger.debug(f"Stop_points : {stop_points}")
    # Read contents of input constraint file
    if stop_points == None:
        stop_points = []
    # TODO: methodology for array layout
    if "array_hier" in name:
        return
    subckt = ckt_data.find(name)
    # Search symmetry constraints
    # TODO move search after processing input const
    match_pairs = FindSymmetry(subckt, stop_points)
    pp = process_input_const(subckt)
    written_symmetries = pp.process_all()
    skip_const = written_symmetries.copy()
    ## Generate hiearchies based on array identification
    array_hier = add_array_const(subckt, match_pairs)
    hier_keys = array_hier.filter_array()
    written_symmetries.extend(hier_keys)
    ## Add symmetry constraints
    add_symm = add_symmetry_const(subckt, match_pairs, stop_points, written_symmetries, skip_const)
    add_symm.loop_through_pairs()

class add_array_const:
    def __init__(self, subckt, match_pairs):
        self.match_pairs = {k: v for k, v in match_pairs.items() if len(v) > 1}
        self.subckt = subckt
        self.name = subckt.name
        self.G = Graph(subckt)
        self.iconst = subckt.constraints
    def filter_hierarchy():
        pass
    def filter_array(self):
        align_const_keys = [key for key, value in self.match_pairs.items() if isinstance(value, list)]
        logger.debug(f"AlignBlock const gen{align_const_keys}")
        check_duplicate = []
        for key in align_const_keys:
            array = self.match_pairs[key]
            logger.debug(f"group1: {array}")
            h_blocks = [ele for ele in array if ele in self.G and ele not in check_duplicate]
            if len(h_blocks) > 0:
                check_duplicate += h_blocks
                self.iconst.append(constraint.AlignBlock(direction="H", instances=h_blocks))
            del self.match_pairs[key]
        logger.debug(f"AlignBlock const update {self.iconst}")
        hier_keys = [key for key, value in self.match_pairs.items() if "name" in value.keys()]
        for key in hier_keys:
            del self.match_pairs[key]
        return hier_keys

class process_input_const:
    def __init__(self, subckt):
        self.written_symblocks = list() # list of set for symmetric pairs and string
        self.subckt = subckt
        self.name = subckt.name
        self.G = Graph(subckt)
        self.iconst = subckt.constraints
    def process_all(self):
        self.process_symmnet()
        return self.written_symblocks
    def process_symmnet(self):
        logger.debug(f"input const {self.iconst}")
        update_symmnet = list()
        for const in self.iconst:
            if isinstance(const, constraint.SymmetricNets):
                # if not getattr(const, 'pins1', None):
                # TODO: constr with pin information should be handled separately
                logger.debug(f"adding pins to user symmnet constraint {const}")
                pairs, s1, s2 = symmnet_device_pairs(
                    self.G, const.net1.upper(), const.net2.upper(), self.written_symmetries, None, True)
                assert s1, f"no connections found to net {const.net1}, fix user const"
                assert s2, f"no connections found to net {const.net2}, fix user const"
                with set_context(self.iconst):
                    update_symmnet.append(
                        (
                            const,
                            constraint.SymmetricNets(
                                direction=const.direction,
                                net1=const.net1.upper(),
                                net2=const.net2.upper(),
                                pins1=s1,
                                pins2=s2,
                            ),
                        )
                    )
                continue
            elif isinstance(const, constraint.DoNotIdentify):
                self.written_symblocks.extend(const.instances)
        for k, v in update_symmnet:
            with set_context(self.iconst):
                self.iconst.remove(k)
                self.iconst.append(v)
                self.written_symblocks.append(v.net1)
                self.written_symblocks.append(v.net2)

class add_symmetry_const:
    def __init__(self, subckt, match_pairs, stop_points, written_symmetries, skip_const):
        self.all_pairs = sorted(
        match_pairs.values(),
        key=lambda k: len([k1 for k1, v1 in k.items() if k1 != v1]),
        reverse=True,
        )
        self.written_symmetries = written_symmetries
        self.subckt = subckt
        self.name = subckt.name
        self.G = Graph(subckt)
        self.iconst = subckt.constraints
        self.stop = stop_points # TODO: Can be removed?
        self.skip_const = skip_const
        logger.debug(f"stop points for hier {subckt.name} are {stop_points}")
        logger.debug(f"excluded input symmetry pairs {self.written_symmetries}")
        logger.debug(f"all symmetry matching pairs {pprint.pformat(self.all_pairs, indent=4)}")

    def loop_through_pairs(self):
        for pairs in self.all_pairs:
            pairs = sorted(pairs.items(), key=lambda k: k[0])
            logger.debug(f"symmblock pairs: {pairs}, existing: {self.written_symmetries}")
            pairsj = self.filter_symblock_const(pairs)
            add_or_revert_const(pairsj, self.iconst, self.written_symmetries)
        for pairs in self.all_pairs:
            pairs = sorted(pairs.items(), key=lambda k: k[0])
            logger.debug(f"symmnet pairs: {pairs}, existing: {self.written_symmetries}")
            pairsj = self.filter_symnet_const(pairs)
            add_or_revert_const(pairsj, self.iconst, self.written_symmetries)
        logger.debug(f"identified constraints of {self.name} are {self.iconst}")

    def pre_fiter(self, key,value):
        if key in self.stop:
            # logger.debug(f"skipping symmetry b/w {key} {value} as they are present in stop points")
            return True
        elif key in self.written_symmetries or value in self.written_symmetries or set([key,value]) in self.written_symmetries:
            # logger.debug(f"skipping symmetry b/w {key} {value} as already written {written_symmetries}")
            return True
        elif key not in self.G.nodes():
            # logger.debug(f"skipping symmetry b/w {key} {value} as {key} is not in graph")
            return True

    def filter_symblock_const(self, pairs: list):
        pairsj = []
        for key, value in pairs:
            if self.pre_fiter(key, value):
                continue
            if not self.G.nodes[key].get("instance"):
                continue
            elif "Dcap" in self.G.nodes[key].get("instance").model:
                logger.debug(f"skipping symmetry for dcaps {key} {value}")
            else:
                bm = get_base_model(self.subckt, key)
                if key == value and bm in ["NMOS", "PMOS", "RES", "CAP"]:
                    logger.debug(f"TBF:skipping self symmetry for single transistor {key}")
                elif key !=value:
                    pairsj.append([key,value])
                else:
                    pairsj.append([key])
        return pairsj

    def filter_symnet_const(self, pairs:list):
        pairsj = []
        for key, value in pairs:
            if self.pre_fiter(key, value):
                continue
            if not self.G.nodes[key].get("instance"):
                if key != value:
                    pairs, s1, s2 = symmnet_device_pairs(self.G, key, value, self.written_symmetries, self.skip_const)
                    if pairs:
                        self.written_symmetries.append({key,value})
                        with set_context(self.iconst):
                            symmnet = constraint.SymmetricNets(
                                direction="V", net1=key, net2=value, pins1=s1, pins2=s2
                            )
                            self.iconst.append(symmnet)
                        logger.debug(f"adding symmetric net const: {symmnet}")
                    else:
                        logger.debug(f"Skip symmetry: large fanout nets {key} {value} {pairs}")
                        # TODO Need update in placer to simplify this
                else:
                    logger.debug(f"skipping self symmetric nets {key} {value}")
        return pairsj

def add_or_revert_const(pairsj: list, iconst, written_symmetries: list):
    logger.debug(f"filterd symmetry pairs: {pairsj}")
    if len(pairsj) > 1 or (pairsj and len(pairsj[0])==2):
        _temp = len(iconst)
        try:
            with set_context(iconst):
                symmBlock = constraint.SymmetricBlocks(direction="V", pairs=pairsj)
                iconst.append(symmBlock)
                written_symmetries.extend([set(pair) for pair in pairsj])
                # written_symmetries.extend([str(ele) for pair in pairsj for ele in pair])
                logger.debug(f"one axis of written symmetries: {symmBlock}")
        except:
            while len(iconst) > _temp:
                iconst.pop()
            logger.debug(f"skipping match {pairsj} due to unsatisfied constraints")
            pass


def symmnet_device_pairs(G, net_A, net_B, smb=list(), skip_blocks=None, user=False):
    """
    Parameters
    ----------
    G : networkx graph
        subckt graphs.
    net_A/B : two nets A/B
        DESCRIPTION.
    sm: existing symmetry blocks list
    Returns
    -------
    pairs : dict
        deviceA/pin: deviceB/pin.
    """
    def _connection(net: str):
        """
        Returns all pins and ports connected to the net
        """
        assert G.nodes(net)
        conn = {}
        logger.debug(f"checking connections of net: {net}, {list(G.neighbors(net))}")
        for nbr in list(G.neighbors(net)):
            pins = G.get_edge_data(net, nbr)["pin"]
            child = G.subckt.parent.find(G.nodes[nbr].get("instance").model)
            if isinstance(child, SubCircuit):
                for pin in pins:
                    leaf_conn = set(sorted([c for c in get_leaf_connection(child, pin) if c != "B"]))
                    if leaf_conn:
                        conn[(nbr,pin)] = leaf_conn
            else:
                for pin in pins:
                    if pin != "B":
                        conn[(nbr,pin)] = [pin]
        if net in G.subckt.pins:
            conn[net] = set(sorted([c for c in get_leaf_connection(G.subckt, net) if c != "B"]))
        return conn
    conn_A = _connection(net_A)
    conn_B = _connection(net_B)
    logger.debug(
        f"Identifying match pairs for symmnet, \
        net1 {net_A}, connections: {conn_A}, \
        net2 {net_B}, connections {conn_B}, \
        existing: {smb}, skip: {skip_blocks}"
    )
    assert conn_A, f"No connection to net {net_A} found in {G.subckt.name}"
    assert conn_B, f"No connection to net {net_A} found in {G.subckt.name}"

    pairs = {}
    pinsA = []
    pinsB = []
    for ele_A in conn_A.keys():
        for ele_B in conn_B.keys():
            #tuple of (block, pin)
            if isinstance(ele_A,tuple) and isinstance(ele_B,tuple):
                logger.debug(f"Check ele_a {ele_A}, ele_B {ele_B}, pairs {pairs}")
                instA = ele_A[0]
                instB = ele_B[0]
                if skip_blocks and (instA in skip_blocks or instB in skip_blocks):
                    logger.debug(f"skipping blocks: {instA},{instB} do_not_identify {skip_blocks}")
                    continue
                instA = G.nodes[instA].get("instance")
                assert instA, f"Block,{instA} not found"
                instB = G.nodes[instB].get("instance")
                assert instB, f"Block,{instB} not found"
                logger.debug(f"modelA:{instA.model} modelB:{instB.model}")
                if (
                    conn_A[ele_A] == conn_B[ele_B]
                    and instA.model == instB.model
                ):
                    logger.debug(f"checking symmetric instances {ele_A}, {ele_B}")
                    if instB in pairs.values():
                        logger.debug(
                            f"Skip symmnet: Multiple matches of net {net_B} nbr {ele_B} to {pairs.values()} "
                        )
                        return [None, None, None]
                    elif user == False and {instA, instB} not in smb:
                        logger.debug(f"unsymmetrical instances {instA, instB} {smb}")
                        continue
                    elif ele_A not in pinsA and ele_B not in pinsB:
                        logger.debug(f"Add symmetric connections {ele_A, ele_B}")
                        pairs[instA] = instB
                        pinsA.append("/".join(ele_A))
                        pinsB.append("/".join(ele_B))
            elif (
                not (isinstance(ele_A, tuple) or isinstance(ele_B, tuple))
                and conn_A[ele_A] == conn_B[ele_B]
                and ele_A not in pinsA
                and ele_B not in pinsB
            ):
                # Ports matching
                logger.debug(f"Add symmetric ports: {ele_A}, {ele_A}")
                pairs[ele_A] = ele_B
                pinsA.append(ele_A)
                pinsB.append(ele_B)

    # Atleast two pair of pins need to be matched
    if len(pairs.keys()) > 1:
        return pairs, pinsA, pinsB
    else:
        logger.debug(
            f"Skip symmnet: Non identical instances {conn_A} {conn_B} {smb}"
        )
        return [None, None, None]
