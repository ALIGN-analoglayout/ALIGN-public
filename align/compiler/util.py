# -*- coding: utf-8 -*-
"""
Created on Tue Dec 11 11:34:45 2018

@author: kunal
"""
from ..schema.graph import Graph
from ..schema import SubCircuit, Model
import logging
import pathlib
import hashlib

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
    model_def = subckt.parent.find(cm)
    assert model_def
    if isinstance(model_def, SubCircuit) and len(model_def.elements) == 1:
        base_model = get_base_model(model_def, model_def.elements[0].name)
    elif isinstance(model_def, Model) and not isinstance(model_def, SubCircuit):
        base_model = subckt.parent.find(cm).base
        if not base_model:
            base_model = cm
    else:
        base_model = cm
    return base_model


def get_leaf_connection(subckt, net):
    # assert net in subckt.nets, f""
    conn = []
    if net in subckt.nets:
        graph = Graph(subckt)
        for nbr in graph.neighbors(net):
            for pin in graph.get_edge_data(net, nbr)["pin"]:
                s = subckt.parent.find(graph.nodes[nbr].get("instance").model)
                if isinstance(s, SubCircuit):
                    conn.extend(get_leaf_connection(s, pin))
                else:
                    conn.append(pin)
    else:
        logger.debug(f"floating net {net} found in subckt {subckt.name} {subckt.nets}")
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


def get_ports_weight(G):
    ports_weight = dict()
    subckt = G.subckt
    for port in subckt.pins:
        leaf_conn = get_leaf_connection(subckt, port)
        # logger.debug(f"leaf connections of net ({port}): {leaf_conn}")
        # assert leaf_conn, f"floating port: {port} in subckt {subckt.name}"
        if leaf_conn:
            ports_weight[port] = set(sorted(leaf_conn))
        else:
            ports_weight[port] = {}
    return ports_weight

def gen_key(param):
    """_gen_key
    Creates a hex key for combined transistor params
    Args:
        param (dict): dictionary of parameters
    Returns:
        str: unique hex key
    """
    skeys = sorted(param.keys())
    arg_str = '_'.join([k+':'+str(param[k]) for k in skeys])
    key = f"_{str(int(hashlib.sha256(arg_str.encode('utf-8')).hexdigest(), 16) % 10**8)}"
    return key

def create_node_id(G, node1, ports_weight=None):
    in1 = G.nodes[node1].get("instance")
    if in1:
        properties = {'model':in1.model,
                      'n_pins':len(set(in1.pins.values()))
        }
        if in1.parameters:
            properties.update(in1.parameters)
        return gen_key(properties)
    else:
        nbrs1 = [nbr for nbr in G.neighbors(node1) if reduced_SD_neighbors(G, node1, nbr)]
        properties = [G.nodes[nbr].get("instance").model for nbr in nbrs1]
        if node1 in ports_weight:
            properties.extend([str(p) for p in ports_weight[node1]])
        else:
            lw = [leaf_weights(G, node1, nbr) for nbr in nbrs1]
            properties.extend([str(p) for p in lw])
        properties = sorted(properties)
        arg_str = '_'.join(properties)
        key = f"_{str(int(hashlib.sha256(arg_str.encode('utf-8')).hexdigest(), 16) % 10**8)}"
        return key


def compare_two_nodes(G, node1: str, node2: str, ports_weight=None):
    """
    compare two node properties. It uses 1st level of neighbourhood for comparison of nets

    Parameters
    ----------
    G : TYPE, networkx graph
        DESCRIPTION. it consist of all subckt properties
    node1, node2 : TYPE  string
        DESCRIPTION. node name
    ports_weight : TYPE list
        DESCRIPTION. port weights

    Returns
    -------
    bool
        DESCRIPTION. True for matching node

    """
    id1 = create_node_id(G,node1, ports_weight=ports_weight)
    id2 = create_node_id(G, node2, ports_weight=ports_weight)
    return id1 ==id2


def get_primitive_spice():
    return pathlib.Path(__file__).resolve().parent.parent / "config" / "basic_template.sp"
