# -*- coding: utf-8 -*-
"""
Created on Wed Feb 21 13:12:15 2020

@author: kunal
"""

from align.schema.types import set_context
import pprint
from itertools import combinations, combinations_with_replacement
import logging

from .create_array_hierarchy import process_arrays
from .util import compare_two_nodes, get_base_model, reduced_neighbors, reduced_SD_neighbors, get_leaf_connection, get_ports_weight
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
    # remove body connections
    G = Graph(G.subckt)
    nbrs1 = sorted(set(G.neighbors(node1)) - traversed)
    nbrs1 = sorted(set([nbr for nbr in nbrs1 if reduced_neighbors(G, node1, nbr)]))
    nbrs2 = sorted(set(G.neighbors(node2)) - traversed)
    nbrs2 = sorted(set([nbr for nbr in nbrs2 if reduced_neighbors(G, node2, nbr)]))
    logger.debug(f"node1:{node1},property: {G.nodes[node1]},neigbors1: {nbrs1}")
    logger.debug(f"node2:{node2},property: {G.nodes[node2]},neigbors2: {nbrs2}")
    if not nbrs1 or not nbrs2:
        if compare_two_nodes(G, node1, node2, ports_weight):
            match_pair[node1] = node2
        logger.debug(f"no new neighbours, returning recursion {match_pair}")
        return
    elif len(nbrs1) > 10:
        assert not match_pair.get("array_start_point", False), f"incorrect symmetry branch"
        # Reset constraints if array hierarchy is generated
        array_hier = process_arrays(G.subckt, {(node1, node2): {"array_start_point": [node1, node2]}})
        array_hier.add_align_block_const()
        if array_hier.add_new_array_hier():
            #update graph
            FindConst(G.subckt)
        logger.debug(f"high fanout nets are start point for arrays: (net, neighbors){node1, nbrs1}")
        traversed.add(node1)
        return

    if node1 == node2:
        if node1 in match_pair.keys() or node1 in match_pair.values():
            logger.debug("avoid existing pair wise symmetry")
            return
        logger.debug(f"single node {node1}, nbrs {nbrs1}, nbr_weight {[G.get_edge_data(node1,nbr) for nbr in nbrs1]}")
        SD_nbrs = [nbr for nbr in nbrs1 if reduced_SD_neighbors(G, node1, nbr)]
        # TBD: filter based on primitive constraints
        # Right now will try to figure out S/D paths
        if len(SD_nbrs) == 0:
            # logger.debug(f"No SD paths found to traverse")
            match_pair[node1] = node1
        elif len(SD_nbrs) == 1:
            # logger.debug(f"traversing single S/D path {SD_nbrs}")
            match_pair[node1] = node1
            traversed.add(node1)
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
            # logger.debug(f"multiple nodes diverging {SD_nbrs}")
            # logger.debug(f"nbr weights: {SD_nbrs} {[G.get_edge_data(node1, nbr)['pin'] for nbr in SD_nbrs]}")
            match_pair[node1] = node1
            traversed.add(node1)
            new_sp = sorted(set(SD_nbrs) - traversed)
            all_match_pairs_local = {}
            for nbr1, nbr2 in combinations(new_sp, 2):
                # logger.debug(f"recursive pair call from single branch {nbr1} {nbr2}")
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
                    all_match_pairs_local[(nbr1, nbr2)] = new_pair
            all_match_pairs_local = {
                k: v for k, v in all_match_pairs_local.items() if len(v) > 0
            }
            if len(all_match_pairs_local) == 1:
                match_pair.update(
                    all_match_pairs_local[list(all_match_pairs_local.keys())[0]]
                )
            else:
                for nbr1 in new_sp:
                    if (nbr1, nbr1) not in match_pairs.keys():
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
                        # filtering multiple axis of symmetries with same block
                        # ideally they should be handled by array generation
                        if new_pair:
                            match_pairs[(nbr1, nbr1)] = new_pair
                            # logger.debug(f"updating match pairs: {pprint.pformat(match_pairs, indent=4)}")

    elif compare_two_nodes(G, node1, node2, ports_weight):
        match_pair[node1] = node2
        traversed.update([node1, node2])
        logger.debug(f"Traversing parallel branches from {node1},{node2} {nbrs1}, {nbrs2}")
        nbrs1_wt = [pin for nbr in nbrs1 for pin in G.get_edge_data(node1, nbr)["pin"]]
        nbrs2_wt = [pin for nbr in nbrs2 for pin in G.get_edge_data(node2, nbr)["pin"]]
        logger.debug(f"nbr1 conn: {nbrs1_wt}, nbr2 {nbrs2_wt}")
        unique_match = find_unique_matching_branches(G, nbrs1, nbrs2, ports_weight)
        if unique_match:
            match_pair[node1] = node2
            traversed.update([node1, node2])
            for nbr1, nbr2 in unique_match.items():
                compare_nodes(G, match_pairs, match_pair, traversed.copy(), nbr1, nbr2, ports_weight)
        elif (
            len(nbrs1_wt) > len(set(nbrs1_wt)) > 1
            and len(nbrs2_wt) > len(set(nbrs2_wt)) > 1
        ):
            logger.debug(f"setting new start points {node1} {node2}")
            match_pair[node1] = node2
            assert not match_pair.get("array_start_point", False), f"incorrect symmetry branch {match_pair} {node1, node2}"
            # Identify arrays
            # Reset constraints if array hierarchy is generated
            logger.debug(f"checking arrays from {node1, node2}")
            array_hier = process_arrays(G.subckt, {(node1, node2): {"array_start_point": [node1, node2]}})
            array_hier.add_align_block_const()
            if array_hier.add_new_array_hier():
                FindConst(G.subckt) #reset const
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
    match_pairs[(node1, node2)] = pair
    logger.debug(f"updated match pairs (start): {pprint.pformat(match_pairs, indent=4)}")
    return


def FindSymmetry(subckt, stop_points: set):
    """
    Find matching constraint starting from all port pairs.
    check: recursive_start_points
    Parameters
    ----------
    stop_points : list
        starts with power, ground and clock signals adds based on traversal.
    Returns
    -------
    match_pairs : dict.

    """
    graph = Graph(subckt)
    ports = subckt.pins
    match_pairs = dict()
    if not stop_points:
        stop_points = set()
    non_power_ports = sorted(set(sorted(ports)) - stop_points)
    ports_weight = get_ports_weight(graph)
    # TODO start from primitives
    for port1, port2 in combinations_with_replacement(non_power_ports, 2):
        traversed = stop_points.copy()
        if ports_weight[port1] == ports_weight[port2] and ports_weight[port2]:
            traversed.update([port1, port2])
            recursive_start_points(graph, match_pairs, traversed, port1, port2, ports_weight)
            match_pairs = {k: v for k, v in match_pairs.items() if len(v) > 0}
            # logger.debug(f"Matches starting from {port1, port2} (final): {pprint.pformat(match_pairs, indent=4)}")
    return match_pairs


def constraint_generator(ckt_data):
    """
    Search for symmetry constraints
    Args:
        ckt_data : ckt library after annotation
    """
    for subckt in ckt_data:
        if not isinstance(subckt, SubCircuit):
            continue
        gen_const = [True for const in subckt.constraints if isinstance(const, constraint.Generator)]
        if not gen_const and not "ARRAY_HIER_" in subckt.name.upper():
            FindConst(subckt)


def FindConst(subckt):
    # Read contents of input constraint file
    stop_points = set()
    auto_constraint = True
    for const in subckt.constraints:
        if isinstance(const, constraint.PowerPorts) or\
                isinstance(const, constraint.GroundPorts) or \
                isinstance(const, constraint.ClockPorts):
            stop_points.update(const.ports)
        elif isinstance(const, constraint.ConfigureCompiler):
            auto_constraint = not const.is_digital and const.auto_constraint
    logger.debug(f"Stop_points : {stop_points}")

    pp = process_input_const(subckt)
    #TODO make it a set instead of list
    written_symmblocks = pp.process_all()
    if not auto_constraint:
        return

    logger.debug(f"Searching constraints for block {subckt.name}")
    # Search symmetry constraints
    match_pairs = FindSymmetry(subckt, stop_points)
    logger.debug(f"match pairs {match_pairs}")
    match_pairs = {k: v for k, v in match_pairs.items() if len(v) > 1}
    # Add symmetry constraints
    skip_const = written_symmblocks.copy()
    add_symm = add_symmetry_const(subckt, match_pairs, stop_points, written_symmblocks, skip_const)
    add_symm.loop_through_pairs()


class process_input_const:
    def __init__(self, subckt):
        self.user_constrained_list = list()  # list of set for symmetric pairs and string
        self.subckt = subckt
        self.name = subckt.name
        self.G = Graph(subckt)
        self.iconst = subckt.constraints

    def process_all(self):
        self.process_symmnet()
        #do not identify captures all instance names from constraints
        self.process_do_not_identify()
        return self.user_constrained_list

    def process_do_not_identify(self):
        for const in self.iconst:
            if isinstance(const, constraint.DoNotIdentify):
                self.user_constrained_list.extend(const.instances)

    def process_symmnet(self):
        logger.debug(f"input const {self.iconst}")
        replace_const = list()
        new_symmblock_const = list()
        for const in self.iconst:
            if isinstance(const, constraint.SymmetricNets):
                if not getattr(const, 'pins1', None):
                    logger.debug(f"adding pins to user symmnet constraint {const}")
                    pairs, s1, s2 = symmnet_device_pairs(
                        self.G,
                        const.net1.upper(),
                        const.net2.upper(),
                        self.user_constrained_list,
                        None,
                        True)
                    assert s1, f"no connections found to net {const.net1} in subcircuit {self.subckt}, fix user const"
                    assert s2, f"no connections found to net {const.net2} in subcircuit {self.subckt}, fix user const"
                    with set_context(self.iconst):
                        replace_const.append(
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
                else: # existing pin information
                    pin_pairs = {}
                    remove_duplicate = []
                    for i in range(len(const.pins1)):
                        if const.pins1[i] in pin_pairs.keys():
                            remove_duplicate.append(i)
                        elif not const.pins1[i] in self.subckt.pins:
                            pin_pairs[const.pins1[i]] = const.pins2[i]
                    for index in sorted(remove_duplicate, reverse=True):
                        del const.pins1[index]
                        del const.pins2[index]
                    logger.info(f"updated symmetry net const: {const}")
                    pairs = {k.split("/")[0]: v.split("/")[0] for k,v in pin_pairs.items()}
                pairsj = list()
                for key, value in pairs.items():
                    if key in self.subckt.pins:
                        continue #net name is same as port name
                    if key != value and {key, value} not in self.user_constrained_list:
                        self.user_constrained_list.append({key, value})
                        pairsj.append([key, value])
                    elif key not in self.user_constrained_list:
                        self.user_constrained_list.append(key)
                        pairsj.append([key])
                if len(pairsj) > 0 and not (len(pairsj) == 1 and len(pairsj[0]) == 1):
                    # Do not generate symmetry constraint for a single instance
                    with set_context(self.iconst):
                        symmBlock = constraint.SymmetricBlocks(direction="V", pairs=pairsj)
                    new_symmblock_const.append(symmBlock)
        with set_context(self.iconst):
            for k, v in replace_const:
                if k!=v: # removing constraint does not remove it from cache and z3 solver, duplicate const is not allowed in solver
                    self.iconst.remove(k)
                    self.iconst.append(v)
                    self.user_constrained_list.append(v.net1)
                    self.user_constrained_list.append(v.net2)
            for symb in new_symmblock_const:
                #avoid subsets
                if not any(set(map(tuple, symb.pairs)).issubset(set(map(tuple, const.pairs)))
                    for const in self.iconst if isinstance(const, constraint.SymmetricBlocks)):
                    self.iconst.append(symb)


class add_symmetry_const:
    def __init__(self, subckt, match_pairs, stop_points, written_symmblocks, skip_const):
        self.all_pairs = sorted(
            match_pairs.values(),
            key=lambda k: len([k1 for k1, v1 in k.items() if k1 != v1]),
            reverse=True,
        )
        self.written_symmblocks = written_symmblocks
        self.subckt = subckt
        self.name = subckt.name
        self.G = Graph(subckt)
        self.iconst = subckt.constraints
        if stop_points:
            self.stop = stop_points
        else:
            self.stop = list()
        self.skip_const = skip_const
        # logger.debug(f"stop points for hier {subckt.name} are {stop_points}")
        # logger.debug(f"excluded input symmetry pairs {self.written_symmblocks}")
        # logger.debug(f"all symmetry matching pairs {pprint.pformat(self.all_pairs, indent=4)} {match_pairs}")

    def loop_through_pairs(self):
        for pairs in self.all_pairs:
            pairs = sorted(pairs.items(), key=lambda k: k[0])
            logger.debug(f"symmblock pairs: {pairs}, existing: {self.written_symmblocks}")
            pairsj = self.filter_symblock_const(pairs)
            add_or_revert_const(pairsj, self.iconst, self.written_symmblocks)
        for pairs in self.all_pairs:
            pairs = sorted(pairs.items(), key=lambda k: k[0])
            logger.debug(f"symmnet pairs: {pairs}, existing: {self.written_symmblocks}")
            self.filter_symnet_const(pairs)
            add_or_revert_const(pairsj, self.iconst, self.written_symmblocks)
        logger.debug(f"identified constraints of {self.name} are {self.iconst}")

    def pre_filter(self, key, value):
        smb_1d = set()
        assert isinstance(key, str), f'invlid instance {key}'
        assert isinstance(value, str), f'invlid instance {value}'
        for inst in self.written_symmblocks:
            # extend list elements to one_d list
            if isinstance(inst, str):
                smb_1d.add(inst)
            else:
                smb_1d.update(inst)
        assert not key in self.stop, f"No constraints should be generated for power ports {key}"
        if {key, value} & smb_1d:
            # logger.debug(f"skipping symmetry b/w {key, value} as already written {self.written_symmblocks}")
            return True
        elif key not in self.G.nodes():
            # logger.debug(f"skipping symmetry b/w {key, value} as {key} is not in graph")
            return True
        elif key in self.subckt.nets and key in self.subckt.nets:
            nbrs1, nbrs2 = self.G.all_neighbors_dist([key, value])
            if nbrs1 != nbrs2:
                # logger.debug(f"all neigbors mismatch {key}:{nbrs1}, {value}:{nbrs2}")
                return True
            else:
                logger.debug(f"all neigbors matched {key}:{nbrs1}, {value}:{nbrs2}")

    def filter_symblock_const(self, pairs: list):
        pairsj = list()
        insts_in_single_symmetry = set()
        for key, value in pairs:
            if self.pre_filter(key, value):
                continue
            if {key, value} & insts_in_single_symmetry:
                continue
            if not self.G.nodes[key].get("instance"):
                continue
            else:
                bm = get_base_model(self.subckt, key)
                if key == value and bm in ["NMOS", "PMOS", "RES", "CAP"]:
                    logger.debug(f"Skipping self symmetry for single device {key}")
                elif key != value:
                    pairsj.append([key, value])
                    insts_in_single_symmetry.update([key, value])
                else:
                    pairsj.append([key])
                    insts_in_single_symmetry.add(key)
        return pairsj

    def filter_symnet_const(self, pairs: list):
        for key, value in pairs:
            if self.pre_filter(key, value):
                continue
            if not self.G.nodes[key].get("instance"):
                if key != value:
                    pairs, s1, s2 = symmnet_device_pairs(
                        self.G,
                        key,
                        value,
                        self.written_symmblocks,
                        self.skip_const
                    )
                    if pairs:
                        self.written_symmblocks.append({key, value})
                        with set_context(self.iconst):
                            symmnet = constraint.SymmetricNets(
                                direction="V",
                                net1=key,
                                net2=value,
                                pins1=s1,
                                pins2=s2
                            )
                            self.iconst.append(symmnet)
                        logger.debug(f"adding symmetric net const: {symmnet}")
                    else:
                        logger.debug(f"Skip symmetry: large fanout nets {key} {value} {pairs}")
                        # TODO Need update in placer to simplify this
                else:
                    logger.debug(f"skipping self symmetric nets {key} {value}")


def add_or_revert_const(pairsj: list, iconst, written_symmblocks: list):
    logger.debug(f"filtered symmetry pairs: {pairsj}")
    if len(pairsj) > 1 or (pairsj and len(pairsj[0]) == 2):
        try:
            with set_context(iconst):
                symmBlock = constraint.SymmetricBlocks(direction="V", pairs=pairsj)
                iconst.append(symmBlock)
                written_symmblocks.extend([set(pair) for pair in pairsj])
                # written_symmblocks.extend([str(ele) for pair in pairsj for ele in pair])
                logger.debug(f"one axis of written symmetries: {symmBlock}")
        except:
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
        logger.debug(f"checking connections of net: {net}, {list(G.neighbors(net))}, port {net in  G.subckt.pins}")
        for nbr in list(G.neighbors(net)):
            pins = G.get_edge_data(net, nbr)["pin"]
            child = G.subckt.parent.find(G.nodes[nbr].get("instance").model)
            if isinstance(child, SubCircuit):
                for pin in pins:
                    leaf_conn = set(sorted([c for c in get_leaf_connection(child, pin) if c != "B"]))
                    if leaf_conn:
                        conn[(nbr, pin)] = leaf_conn
            else:
                for pin in pins:
                    if pin != "B":
                        conn[(nbr, pin)] = [pin]
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
            # tuple of (block, pin)
            if isinstance(ele_A, tuple) and isinstance(ele_B, tuple):
                instA_name = ele_A[0]
                instB_name = ele_B[0]
                if skip_blocks and (instA_name in skip_blocks or instB_name in skip_blocks):
                    logger.debug(f"skipping blocks: {instA_name},{instB_name} do_not_identify {skip_blocks}")
                    continue
                instA = G.nodes[instA_name].get("instance")
                assert instA, f"Block,{instA_name} not found"
                instB = G.nodes[instB_name].get("instance")
                assert instB, f"Block,{instB_name} not found"
                logger.debug(f"modelA:{instA.model} modelB:{instB.model}")
                if (
                    conn_A[ele_A] == conn_B[ele_B]
                    and instA.model == instB.model
                ):
                    if instB_name in pairs.values():
                        # logger.debug(
                        #     f"Skip symmnet: Multiple matches of net {net_B} found"
                        # )
                        return [None, None, None]
                    elif not user and {instA_name, instB_name} not in smb:
                        logger.debug(f"unsymmetrical instances {instA_name, instB_name} {smb}")
                        continue
                    elif ele_A not in pinsA and ele_B not in pinsB:
                        logger.debug(f"Add symmetric connections {ele_A, ele_B}")
                        pairs[instA_name] = instB_name
                        pinsA.append("/".join(ele_A))
                        pinsB.append("/".join(ele_B))
            elif (
                not (isinstance(ele_A, tuple) or isinstance(ele_B, tuple))
                and conn_A[ele_A] == conn_B[ele_B]
                and ele_A not in pinsA
                and ele_B not in pinsB
            ):
                # Ports matching
                logger.debug(f"Add symmetric ports: {ele_A}, {ele_B}")
                pairs[ele_A] = ele_B
                pinsA.append(ele_A)
                pinsB.append(ele_B)

    # Atleast two pair of pins need to be matched
    if len(pairs.keys()) > 1:
        logger.debug(f"found pairs {pairs}")
        return pairs, pinsA, pinsB
    else:
        logger.debug(f"Skip symmnet: Non identical instances {conn_A} {conn_B} {smb}")
        return [None, None, None]
