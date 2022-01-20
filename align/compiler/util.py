# -*- coding: utf-8 -*-
"""
Created on Tue Dec 11 11:34:45 2018

@author: kunal
"""
from ..schema.graph import Graph
from ..schema import SubCircuit, Model
import logging
import pathlib

logger = logging.getLogger(__name__)


def get_next_level(subckt, G, tree_l1):
    """get_next_level traverse graph and get next connected element
    Does not traverse Connections through Gate or Body of transistors identified as 'B','G' pins
    TODO: check this skip hierarchically

    [extended_summary]

    Args:
        subckt ([type]): [description]
        G ([type]): [description]
        tree_l1 ([type]): [description]

    Returns:
        [type]: [description]
    """
    tree_next = []
    for node in list(tree_l1):
        assert (
            subckt.get_element(node) or node in subckt.nets
        ), f"{node} not present in {subckt.elements} {subckt.nets}"
        if (
            subckt.get_element(node)
            and get_base_model(subckt, node)
            and "MOS" in get_base_model(subckt, node)
        ):
            for nbr in list(G.neighbors(node)):
                if set(G.get_edge_data(node, nbr)["pin"]) - set({"G", "B"}):
                    tree_next.append(nbr)
        elif node in subckt.nets:
            for nbr in list(G.neighbors(node)):
                base_model = get_base_model(subckt, nbr)
                if (
                    base_model
                    and "MOS" in base_model
                    and set(G.get_edge_data(node, nbr)["pin"]) - set({"G", "B"})
                ):
                    tree_next.append(nbr)
                else:
                    tree_next.append(nbr)
        else:
            tree_next.extend(list(G.neighbors(node)))
    return tree_next


def get_base_model(subckt, node):
    assert subckt.get_element(node), f"node {node} not found in subckt {subckt}"
    cm = subckt.get_element(node).model
    sub_subckt = subckt.parent.find(cm)
    if not sub_subckt:
        # base model
        base_model = cm
    elif isinstance(sub_subckt, SubCircuit) and len(sub_subckt.elements) == 1:
        base_model = get_base_model(sub_subckt, sub_subckt.elements[0].name)
    elif isinstance(sub_subckt, Model):
        temp = subckt.parent.find(cm).base
        if temp:
            base_model = subckt.parent.find(cm).base
        else:
            base_model = cm
    else:
        base_model = cm
    assert base_model, f"base model for {node.name} is {base_model}"
    return base_model


def get_leaf_connection(subckt, net):
    assert net in subckt.nets, f"Net {net} not found in subckt {subckt.name} {subckt.nets}"
    graph = Graph(subckt)
    conn = []
    for nbr in graph.neighbors(net):
        for pin in graph.get_edge_data(net, nbr)["pin"]:
            s = subckt.parent.find(graph.nodes[nbr].get("instance").model)
            if isinstance(s, SubCircuit):
                conn.extend(get_leaf_connection(s, pin))
            else:
                conn.append(pin)
    return conn


def leaf_weights(G, node, nbr):
    subckt = G.subckt
    if subckt.get_element(node):
        assert nbr in subckt.nets, f"net {nbr} not in {subckt.name}"
        n = subckt.get_element(node)
        s = subckt.parent.find(n.model)
        assert nbr in n.pins.values(), f"net {nbr} not connected to {n.name}, {n.pins}"
        p = list(n.pins.keys())[list(n.pins.values()).index(nbr)]
        if isinstance(s, SubCircuit):
            conn_type = set(get_leaf_connection(s, p))
        else:
            conn_type = G.get_edge_data(node, nbr)["pin"]
    else:
        assert node in subckt.nets, f"net {node} not in {subckt.name}"
        n = subckt.get_element(nbr)
        s = subckt.parent.find(n.model)
        assert (node in n.pins.values()), f"net {node} not connected to {n.name}, {n.pins}"
        p = list(n.pins.keys())[list(n.pins.values()).index(node)]
        if isinstance(s, SubCircuit):
            conn_type = set(get_leaf_connection(s, p))
        else:
            conn_type = G.get_edge_data(node, nbr)["pin"]
    return conn_type


def reduced_neighbors(G, node, nbr):
    conn_type = leaf_weights(G, node, nbr)
    if conn_type != {"B"}:
        return True
    else:
        return False


def reduced_SD_neighbors(G, node, nbr):
    conn_type = leaf_weights(G, node, nbr)
    if conn_type-{"B", "G"}:
        return True
    else:
        return False


def get_ports_connection(G):
    ports_conn = dict()
    subckt = G.subckt
    for port in subckt.pins:
        leaf_conn = get_leaf_connection(subckt, port)
        logger.debug(f"leaf connections of net ({port}): {leaf_conn}")
        assert leaf_conn, f"floating port:{port} in subckt {subckt.name}"
        ports_conn[port] = set(sorted(leaf_conn))
    return ports_conn


def compare_two_nodes(G, node1: str, node2: str, ports_conn=None):
    """
    compare two node properties. It uses 1st level of neighbourhood for comparison of nets

    Parameters
    ----------
    G : TYPE, networkx graph
        DESCRIPTION. it consist of all subckt properties
    node1, node2 : TYPE  string
        DESCRIPTION. node name
    ports_conn : TYPE list
        DESCRIPTION. port weights

    Returns
    -------
    bool
        DESCRIPTION. True for matching node

    """
    nbrs1 = [nbr for nbr in G.neighbors(node1) if reduced_SD_neighbors(G, node1, nbr)]
    nbrs2 = [nbr for nbr in G.neighbors(node2) if reduced_SD_neighbors(G, node2, nbr)]
    logger.debug(f"comparing_nodes: {node1}, {node2}, {nbrs1}, {nbrs2}")
    if not ports_conn:
        ports_conn = get_ports_connection(G)
    if G.nodes[node1].get("instance"):
        logger.debug(f"checking match between {node1} {node2}")
        in1 = G.nodes[node1].get("instance")
        in2 = G.nodes[node2].get("instance")
        if (
            in1.model == in2.model
            and len(set(in1.pins.values())) == len(set(in2.pins.values()))
            and in1.parameters == in2.parameters
        ):
            logger.debug(" True")
            return True
        else:
            logger.debug(" False, value mismatch")
            return False
    else:
        nbrs1_type = sorted([G.nodes[nbr].get("instance").model for nbr in nbrs1])
        nbrs2_type = sorted([G.nodes[nbr].get("instance").model for nbr in nbrs2])
        if nbrs1_type != nbrs2_type:
            logger.debug(
                f"type mismatch {nbrs1}:{nbrs1_type} {nbrs2}:{sorted(nbrs2_type)}"
            )
            return False
        if node1 in ports_conn and node2 in ports_conn:
            if sorted(ports_conn[node1]) == sorted(ports_conn[node2]):
                logger.debug("True")
                return True
            else:
                logger.debug(f"external port weight mismatch {ports_conn[node1]},{ports_conn[node2]}")
                return False
        else:
            weight1 = sorted([leaf_weights(G, node1, nbr) for nbr in nbrs1])
            weight2 = sorted([leaf_weights(G, node2, nbr) for nbr in nbrs2])
            if weight2 == weight1:
                logger.debug("True")
                return True
            else:
                logger.debug(f"Internal port weight mismatch {weight1},{weight2}")
                return False


def get_primitive_spice():
    return pathlib.Path(__file__).resolve().parent.parent / "config" / "basic_template.sp"
