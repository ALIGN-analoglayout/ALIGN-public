# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 22:19:39 2018

@author: kunal
"""
import networkx as nx
#from networkx.algorithms import isomorphism

import logging
logger = logging.getLogger(__name__)

def merge_nodes(G, hier_type, argv, matched_ports):
    """ Merges the  given nodes in argv and returns a
     reduced graph. It also returns a subgraph(not used anymore)"""

    #g_copy = G.copy()
    for node in argv:
        if not G.nodes[node]:
            logger.debug("node not in graph anymore")
            return G, nx.Graph
    logger.debug(f"Is input bipartite: {nx.is_bipartite(G)}")
    assert len(argv) > 1
    #  print("Merging nodes",argv)
    new_node = ""
    ports = {}
    subgraph = nx.Graph()
    max_value = {}
    for node in argv:
        new_node += '_' + node
        subgraph.add_node(node,
                          inst_type=G.nodes[node]["inst_type"],
                          real_inst_type=G.nodes[node]["real_inst_type"],
                          ports=G.nodes[node]['ports'],
                          edge_weight=G.nodes[node]['edge_weight'],
                          values=merged_value({},G.nodes[node]['values']))

        max_value = merged_value(max_value, G.nodes[node]['values'])

        nbr = G.neighbors(node)
        for ele in nbr:
            if ele not in subgraph.nodes():
                subgraph.add_node(ele,
                                  inst_type=G.nodes[ele]["inst_type"],
                                  net_type=G.nodes[ele]["net_type"])

            #print("adding edge b/w:",node,ele,G[node][ele]["weight"])
            subgraph.add_edge(node, ele, weight=G[node][ele]["weight"])

            if ele in ports:
                ports[ele] += G[node][ele]["weight"]
            else:
                ports[ele] = G[node][ele]["weight"]


    new_node = new_node[1:]
    G.add_node(new_node,
               inst_type=hier_type,
               real_inst_type=hier_type,
               ports_match=matched_ports,
               values=max_value)
    logger.debug(f"creating a super node of combination of nodes: {hier_type}")
    for pins in list(ports):
        if set(G.neighbors(pins)) <= set(argv) and G.nodes[pins]["net_type"]=='internal':
            del ports[pins]
            G.remove_node(pins)
    for node in argv:
        G.remove_node(node)
    for pins in ports:
        G.add_edge(new_node, pins, weight=ports[pins])
        logger.debug(f"new ports: {pins},{ports[pins]}")

    check_nodes(subgraph)

    return G, subgraph



#%%
def convert_unit(value):
    #print("checking value",value)
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
    elif 'K' in value and is_val:
        value = float(value.replace('K', ""))
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
        #value='{:.2e}'.format(float(re.sub("[^0-9]", "", value)))
        value = float(value.replace('f', ""))
        value = value * 1e-15
    else:
        try:
            value = float(value)
        except ValueError:
            logger.error(f"Parameter {value} not defined. Using value=12n. Please fix netlist")
            value = 1e-8
    return mult*value

def check_values(values):
    for param,value in values.items():
        #print("param,value:%s,%s", param,value)
        assert(type(value)==int or type(value)==float)

def check_nodes(graph):
    """ Checking node paramters to be dict type"""
    for node, attr in graph.nodes(data=True):
        if  not attr["inst_type"] == "net":
            check_values(attr["values"])

def merged_value(values1, values2):
    """
    combines values of different devices:
        right now since primitive generator takes only one value we use max value
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
            merged_vals[param] = convert_unit(value)
    for param,value in values2.items():
        if param in merged_vals.keys():
            merged_vals[param] = max(convert_unit(value), merged_vals[param])
        else:
            merged_vals[param] = convert_unit(value)
    check_values(merged_vals)
    return merged_vals

