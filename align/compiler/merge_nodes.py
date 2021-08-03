# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 22:19:39 2018

@author: kunal

"""
import networkx as nx
from ..schema.instance import Instance
from ..schema.types import set_context
from ..schema.subcircuit import Model, SubCircuit, Circuit, Instance

import logging
logger = logging.getLogger(__name__)
# TODO: rewrite this for caps, array, groupblocks, groupcaps

def merge_nodes(G: nx.classes.graph.Graph, new_inst_type: str, list_of_nodes: list, matched_ports: dict,new_inst_name=None):

    """
    Merges the  given nodes in list_of_nodes and returns a
     reduced graph.

    Parameters
    ----------
    G : netowrkx graph
        DESCRIPTION. Bipartite graph of circuit
    new_inst_type : str
        DESCRIPTION. name of new subckt to be created,
        A super node is created in graph havinge a subgraph in its values
    list_of_nodes : list
        DESCRIPTION.
    matched_ports : dict
        DESCRIPTION. dictionary of {subkt port: connected net} be added in dubckt

    Returns
    -------
    G : nx.classes.graph.Graph
        returns updated graph.

    """
    for node in list_of_nodes:
        if not G.nodes[node]:
            logger.debug("node not in graph anymore")
            return G, nx.Graph
    logger.debug(f"Is input bipartite: {nx.is_bipartite(G)}")
    assert len(list_of_nodes) > 1
    new_node = []
    real_inst_types = []
    ports = {}
    subckt = SubCircuit(
        name = new_inst_type,
        pins = list(matched_ports.keys()),
        parameters = {'PARAM':1})
    max_value = {}
    for node in list_of_nodes:
        new_node.append ( node)
        if G.nodes[node]["instance"].model not in real_inst_types:
            real_inst_types.append (G.nodes[node]["instance"].model)
        subckt.elements.append(G.nodes[node]["instance"])

        logger.debug(f"removing node: {node}: attr: {G.nodes[node]}")
        max_value = merged_value(max_value, G.nodes[node]["instance"].parameters)

    if len(real_inst_types)==1:
        real_inst_types=real_inst_types[0]
    new_node='_'.join(new_node)
    if new_inst_name:
        new_node=new_inst_name
    logger.debug(f"creating a super node of: {new_inst_type} type: {real_inst_types}")
    for pins in list(ports):
        if set(G.neighbors(pins)) <= set(list_of_nodes) and G.nodes[pins]["net_type"]=='internal':
            del ports[pins]
            G.remove_node(pins)
    for node in list_of_nodes:
        G.remove_node(node)
    for pins in ports:
        G.add_edge(new_node, pins, weight=ports[pins])
    return  subckt,new_node

#%%
def convert_unit(value:str):
    """

    Parameters
    ----------
    value : str
        DESCRIPTION.

    Returns
    -------
    float
        DESCRIPTION. converts values to equivalent values

    """
    mult =1
    if type(value)==float or type(value)== int:
        value = value
    elif '*' in value:
        value_function = value.split('*')
        #total =1
        value = 1
        for val in value_function:
            try:
                mult = mult*int(val)
            except:
                value = val
    try:
        float(value[0:-1])
        is_val =True
    except (ValueError, TypeError):
        is_val =False
    if isinstance(value, float) or isinstance(value, int):
        value = value
    elif value.endswith('k') and is_val:
        value = float(value.replace('k', ""))
        value = value * 1000
    elif 'm' in value and is_val:
        value = float(value.replace('m', ""))
        value = value * 1E6
    elif 'p' in value and is_val:
        value = float(value.replace('p', ""))
        value = value * 1E-12
    elif 'n' in value and is_val:
        value = float(value.replace('n', ""))
        value = value * 1E-9
    elif 'u' in value and is_val:
        value = float(value.replace('u', ""))
        value = value * 1E-6
    elif 'f' in value and is_val:
        value = float(value.replace('f', ""))
        value = value * 1e-15
    elif value == "unit_size":
        value = value
    else:
        try:
            value = float(value)
        except ValueError:
            logger.error(f"Parameter {value} not defined. Using value=unit_size. Please fix netlist")
            value = "unit_size"
    return mult*value

def merge_subckt_param(ckt):
    max_value = {}
    for element in ckt.elements:
        max_value = merged_value(max_value, element.parameters)
    return max_value

def merged_value(values1, values2):
    """
    combines values of different devices:
    (right now since primitive generator takes only one value we use max value)
    try:
    #val1={'res': '13.6962k', 'l': '8u', 'w': '500n', 'm': '1'}
    #val2 = {'res': '13.6962k', 'l': '8u', 'w': '500n', 'm': '1'}
    #merged_value(val1,val2)

    Parameters
    ----------
    values1 : TYPE. dict
        DESCRIPTION. dict of parametric values
    values2 : TYPE. dict
        DESCRIPTION.dict of parametric values

    Returns
    -------
    merged_vals : TYPE dict
        DESCRIPTION. max of each parameter value

    """
    merged_vals={}
    if values1:
        for param,value in values1.items():
            merged_vals[param] = value
    for param,value in values2.items():
        if param in merged_vals.keys():
            merged_vals[param] = max(value, merged_vals[param])
        else:
            merged_vals[param] = value
    # check_values(merged_vals)
    return merged_vals

