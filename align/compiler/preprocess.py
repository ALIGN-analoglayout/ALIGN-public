#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Sep 17 15:49:33 2020

@author: kunal001
"""

from .merge_nodes import convert_unit
from .util import get_next_level

import logging
import networkx as nx
import copy

logger = logging.getLogger(__name__)

def remove_pg_pins(hier_graph_dict:dict,circuit_name, pg_pins):
    """
    removes power pins to be sent as signal by recursively finding all connections to power pins 
    and removing them from subcircuit definition and instance calls
    for each circuit different power connection creates an extra subcircuit
    Required by PnR as it does not make power connections as ports
    Parameters
    ----------
    hier_graph_dict : dict
        dictionary of all circuit in spice file
    circuit_name : str
        name of circuit to be processed.
    G : networkx graph
        graph of circuit.
    pg_pins : list
        graph of circuit.
    Returns
    -------
    None.

    """
    G = hier_graph_dict[circuit_name]["graph"]
    logger.debug(f"checking pg ports in {circuit_name} {pg_pins}")
    for node, attr in G.nodes(data=True):
        if 'sub_graph' not in attr or attr['inst_type'] =='net' or not attr["connection"]:
            continue
        elif len(set(attr["connection"].values()) & set(pg_pins))>0:
            logger.debug(f"node: {node} connections {attr['connection']} {attr['ports']}")
            pg_conn = {}
            for k,v in attr["connection"].items():
                if v in pg_pins and k not in pg_pins:
                    pg_conn[k]=v
            if pg_conn:
                logger.debug(f"removing power pin connected as signal net {pg_conn} in {node}")
                #deleting power connections to subcircuits
                for k,v in pg_conn.items():
                    del attr["connection"][k]
                    del attr['edge_weight'][attr["ports"].index(v)]
                    attr["ports"].remove(v)
                #create a new subcircuit and changes its ports to power ports
                #power ports are not written during verilog
                updated_name = modify_pg_conn_subckt(hier_graph_dict,attr["inst_type"], pg_conn)
                attr["inst_type"] = updated_name
                remove_pg_pins(hier_graph_dict,updated_name, pg_pins)
                
def modify_pg_conn_subckt(hier_graph_dict:dict,circuit_name, pg_conn):
    """
    creates a new subcircuit by removing power pins from a subcircuit definition 
    and change internal connections within the subcircuit
   
    Parameters
    ----------
    hier_graph_dict : dict
        dictionary of all circuit in spice file
    circuit_name : str
        name of circuit to be processed.
    pg_conn : dict
        ports to be modified and corresponding pg pin.
    Returns
    -------
    new subcircuit name

    """

    new = copy.deepcopy(hier_graph_dict[circuit_name])
    logger.debug(f"modifying subckt {circuit_name} {new} {pg_conn}")
    for k,v in pg_conn.items():
        logger.debug(f"fixing port {k} to {v} for all inst in {circuit_name}")
        new["ports"].remove(k)
        del new["ports_weight"][k]
        if v in new["graph"].nodes():
            old_edge_wt=list(copy.deepcopy(new["graph"].edges(v,data=True)))
            new["graph"] = nx.relabel_nodes(new["graph"],{k:v},copy=False)
            for n1,n2,v1 in new["graph"].edges(v,data=True):
                for n11,n21,v11 in old_edge_wt:
                    if n1 == n11 and n2 ==n21:
                        v1["weight"] = v1["weight"] | v11["weight"]
            logger.debug(f"updated weights {old_edge_wt} {new['graph'].edges(v,data=True)}")

        else:
            new["graph"] = nx.relabel_nodes(new["graph"],{k:v},copy=False)

        for node,attr in new["graph"].nodes(data=True):
            if attr["inst_type"]=='net':
                continue
            #if k in attr["ports"]:
            #logger.debug(f"updating node {node} {attr}")
            attr["ports"]=[v if x==k else x for x in attr["ports"]]
            if "connection" in attr and attr["connection"]:
                for a,b in attr["connection"].items():
                    if b==k:
                        attr["connection"][a]=v
                        logger.debug(f"updated attributes of {node}: {attr}")
                
    i=1
    updated_ckt_name = circuit_name+'pg'+str(i)
    while updated_ckt_name in hier_graph_dict.keys():
        if hier_graph_dict[updated_ckt_name]["ports"]==new["ports"]:
            break
        else:
            i = i+1
            updated_ckt_name = circuit_name+'pg'+str(i)
    hier_graph_dict[ updated_ckt_name] = new   
    return updated_ckt_name


def preprocess_stack_parallel(hier_graph_dict:dict,circuit_name,G):
    """
    Preprocess the input graph by reducing parallel caps, series resistance, identify stacking, adding parallel transistors.

    Parameters
    ----------
    hier_graph_dict : dict
        dictionary of all circuit in spice file
    circuit_name : str
        name of circuit to be processed.
    G : networkx graph
        graph of circuit.

    Returns
    -------
    None.

    """
    logger.debug(f"no of nodes: {len(G)}")
    add_parallel_caps(G)
    add_series_res(G)
    add_stacked_transistor(G)
    add_parallel_transistor(G)
    initial_size=len(G)
    delta =1
    while delta > 0:
        logger.debug(f"CHECKING stacked transistors {circuit_name} {G}")
        add_stacked_transistor(G)
        add_parallel_transistor(G)
        delta = initial_size - len(G)
        initial_size = len(G)
    #remove single instance subcircuits 
    attributes = [attr for node, attr in G.nodes(data=True) if 'net' not in attr["inst_type"]]
    if len(attributes)==1:
        #Check any existing hier
        if 'sub_graph' in attributes[0].keys() and attributes[0]['sub_graph'] is not None:
            logger.debug(f"sub_graph nodes {attributes[0]['sub_graph'].nodes()}")
            stacked_ckt = preprocess_stack_parallel(hier_graph_dict,attributes[0]["real_inst_type"],attributes[0]["sub_graph"])
            if stacked_ckt ==None:
                return None

        for ckt in hier_graph_dict.values():
            for node,attr in ckt["graph"].nodes(data=True):
                if 'net' not in attr["inst_type"] and attr["inst_type"]==circuit_name:
                    logger.debug(f"updating instance {node} {attr} with stacked device {attributes}")
                    attr["inst_type"]=attributes[0]["inst_type"]
                    attr["real_inst_type"]=attributes[0]["real_inst_type"]
                    attr["values"]={**attributes[0]["values"],**attr["values"]}
                    attr["sub_graph"] =None
                    attr["ports"] =[attr["connection"][port] for port in attributes[0]["ports"] if port in attr["connection"]]
                    attr["edge_weight"] = attributes[0]["edge_weight"]
                    attr["connection"]= None
                                                                   
        return circuit_name
    else:
        return None
        
   
def change_SD(G,node):
    nbr = list(G.neighbors(node))
    #No gate change
    nbr = [nr for nr in nbr if G.get_edge_data(node, nr)['weight']!=2 and G.get_edge_data(node, nr)['weight']!=8]
    #Swapping D and S
    w1 = G.get_edge_data(node, nbr[0])['weight']
    w2 = G.get_edge_data(node, nbr[1])['weight']
    logger.debug(f"Swapping D and S {nbr} {w1} {w2}")
    if w1 & 1:
        w1 = w1 +3
        w2 = w2 -3
    elif w1 & 4:
        w1 = w1-3
        w2 = w2 +3 

    G.get_edge_data(node, nbr[0])['weight'] = w1
    G.get_edge_data(node, nbr[1])['weight'] = w2

def define_SD(circuit,power,gnd,clk):
    logger.debug(f"START checking source and drain in graph ")
    G= circuit["graph"]
    ports = circuit["ports"]
    if power and gnd:
        high= list(set(power).intersection(set(ports)))
        low = list(set(gnd).intersection(set(ports)))
        logger.debug(f"using power: {high} and ground: {low}")
    else:
        logger.warning("Power and ground nets not specified")
        return False
    if not high or not low:
        logger.info('no power and gnd in this circuit')
        return 
    probable_changes_p=[]
    if high[0] in G.nodes():
        traversed = high.copy()
        while high:
            try:
                nxt = high.pop(0)
                for node in get_next_level(G,[nxt]):
                    if G.get_edge_data(node,nxt)==2 or node in traversed:
                        continue
                    # if set(G.neighbors(node)) & set(clk):
                    #     continue
                    logger.debug("VDD:checking node: %s %s %s ", node, high,traversed)
                    if 'pmos' == G.nodes[node]["inst_type"] and \
                        node not in traversed:
                        weight =G.get_edge_data(node, nxt)['weight'] & ~ 8
                        if weight == 1 or weight==3 :
                            # logger.debug("VDD:probable change source drain:%s",node)
                            probable_changes_p.append(node)
                    elif 'nmos' == G.nodes[node]["inst_type"] and \
                    node not in traversed:
                        weight =G.get_edge_data(node, nxt)['weight'] & ~ 8
                        if weight == 4 or weight==6 :
                            # logger.debug("VDD:probable change source drain:%s",node)
                            probable_changes_p.append(node)
                    if node not in traversed and node not in  gnd:
                        high.append(node)
                    traversed.append(node)
            except (TypeError, ValueError):
                logger.debug(f"All source drain checked: {high}")
                break
    probable_changes_n=[]
    if low[0] in G.nodes():
        traversed=low.copy()
        while low:
            try:
                nxt = low.pop(0)
                for node in get_next_level(G,[nxt]):
                    if G.get_edge_data(node,nxt)==2 or node in traversed:
                        continue
                    # if set(G.neighbors(node)) & set(clk):
                    #     continue
                    logger.debug("GND:checking node: %s %s %s ", node, low,traversed)
                    if 'pmos' == G.nodes[node]["inst_type"] and \
                        node not in traversed:
                        weight =G.get_edge_data(node, nxt)['weight'] & ~ 8
                        if weight == 4 or weight==6 :
                            # logger.debug("GND:probable change source drain:%s",node)
                            probable_changes_n.append(node)
                    elif 'nmos' == G.nodes[node]["inst_type"] and \
                    node not in traversed:
                        weight =G.get_edge_data(node, nxt)['weight'] & ~ 8
                        if weight == 1 or weight==3 :
                            # logger.debug("GND:probable change source drain:%s",node)
                            probable_changes_n.append(node)
                    if node not in traversed and node not in  power:
                        low.append(node)
                    traversed.append(node)
            except (TypeError, ValueError):
                logger.debug(f"All source drain checked: {low}")
                break
    for node in list (set(probable_changes_n) & set(probable_changes_p)):
        logger.info(f"changing source drain: {node}")
        change_SD(G,node)


def add_parallel_caps(G):
    logger.debug(f"merging all caps, initial graph size: {len(G)}")
    remove_nodes = []
    for node, attr in G.nodes(data=True):
        if 'cap' in attr["inst_type"] and node not in remove_nodes:
            for net in G.neighbors(node):
                for next_node in G.neighbors(net):
                    if not next_node == node  and next_node not in remove_nodes and G.nodes[next_node][
                        "inst_type"] == G.nodes[node]["inst_type"] and\
                        len(set(G.neighbors(node)) & set(G.neighbors(next_node)))==2:
                        for param, value in G.nodes[node]["values"].items():
                            if param == 'cap':
                                c_val = float(convert_unit(value))+ \
                                float(convert_unit(G.nodes[next_node]["values"]['cap']))
                                remove_nodes.append(next_node)
                                G.nodes[node]["values"]['cap']=c_val
                            elif param == 'c':
                                c_val = float(convert_unit(value))+ \
                                float(convert_unit(G.nodes[next_node]["values"]['c']))
                                remove_nodes.append(next_node)
                                G.nodes[node]["values"]['c']=c_val
    if len(remove_nodes)>0:
        logger.debug(f"removed parallel caps: {remove_nodes}")
        for node in remove_nodes:
            G.remove_node(node)
            
def add_series_res(G):
    logger.debug(f"merging all series res, initial graph size: {len(G)}")
    remove_nodes = []
    for net, attr in G.nodes(data=True):
        if 'net' in attr["inst_type"] and len(set(G.neighbors(net)))==2 \
            and net not in remove_nodes and attr["net_type"]!="external":
            nbr_type =[G.nodes[nbr]["inst_type"] for nbr in list(G.neighbors(net))]
            combined_r,remove_r=list(G.neighbors(net))
            if nbr_type[0]==nbr_type[1]=='res':
                remove_nodes+=[net,remove_r]
                new_net=list(set(G.neighbors(remove_r))-set(net)-set(remove_nodes))[0]
                for param, value in G.nodes[combined_r]["values"].items():
                    if param == 'res':
                        r_val = float(convert_unit(value))+ \
                        float(convert_unit(G.nodes[remove_r]["values"]['res']))
                        G.nodes[combined_r]["values"]['res']=r_val
                        G.add_edge(combined_r, new_net, weight=G[combined_r][net]["weight"])
                    elif param == 'r':
                        r_val = float(convert_unit(value))+ \
                        float(convert_unit(G.nodes[remove_r]["values"]['r']))
                        G.nodes[combined_r]["values"]['r']=r_val
                        G.add_edge(combined_r, new_net, weight=G[combined_r][net]["weight"])
    if len(remove_nodes)>0:
        logger.debug(f"removed series r: {remove_nodes}")
        for node in remove_nodes:
            G.remove_node(node)
        #to remove 3 in series
        add_series_res(G)
def add_parallel_transistor(G):
    logger.debug(f"CHECKING parallel transistors, initial graph size: {len(G)}")
    remove_nodes = []
    for node, attr in G.nodes(data=True):
        if 'mos' in attr["inst_type"] and node not in remove_nodes:
            for net in G.neighbors(node):
                for next_node in G.neighbors(net):
                    
                    if not next_node == node  and next_node not in remove_nodes and G.nodes[next_node][
                        "inst_type"] == G.nodes[node]["inst_type"] and G.nodes[next_node][
                        "values"] == G.nodes[node]["values"] and \
                        set(G.neighbors(node)) == set(G.neighbors(next_node)):
                        nbr_wt_node=[G.get_edge_data(node, nbr)['weight'] for nbr in G.neighbors(node)]
                        nbr_wt_next_node=[G.get_edge_data(next_node, nbr)['weight'] for nbr in G.neighbors(node)]
                        if nbr_wt_node != nbr_wt_next_node:
                            #cross connections
                            continue
                        if 'm' in G.nodes[node]["values"]:
                            remove_nodes.append(next_node)
                            G.nodes[node]["values"]['m']=2*float(convert_unit(G.nodes[node]["values"]['m']))
                        else:
                            remove_nodes.append(next_node)
                            G.nodes[node]["values"]['m']=2
    if len(remove_nodes)>0:
        logger.debug(f"removed parallel transistors: {remove_nodes}")
        for node in remove_nodes:
            G.remove_node(node)
def add_stacked_transistor(G):
    """
    Reduce stacked transistors
    Parameters
    ----------
    G : networkx graph
        input graph

    Returns
    -------
    None.

    """
    logger.debug(f"START reducing  stacks in graph: {G.nodes(data=True)} {G.edges()} ")
    logger.debug(f"initial size of graph: {len(G)}")
    remove_nodes = []
    modified_edges = {}
    modified_nodes = {}
    for node, attr in G.nodes(data=True):
        if 'mos' in attr["inst_type"] and node not in remove_nodes:
            for net in G.neighbors(node):
                edge_wt = G.get_edge_data(node, net)['weight'] & ~8
                #for source nets with only two connections
                if edge_wt == 4 and len(list(G.neighbors(net))) == 2:
                    for next_node in G.neighbors(net):
                        logger.debug(f" checking nodes: {node}, {next_node} {net} {modified_nodes} {remove_nodes} ")
                        if len( {node,next_node}- (set(modified_nodes.keys()) | set(remove_nodes)) )!=2:
                            logger.debug(f"skipping {node} {next_node} as they are same or accessed before")
                            continue
                        elif not next_node == node and G.nodes[next_node][
                                "inst_type"] == G.nodes[node][
                                    "inst_type"] and G.get_edge_data(
                                        next_node, net)['weight'] == 1:
                            common_nets = set(G.neighbors(node)) & set( G.neighbors(next_node))
                            # source net of neighbor
                            source_net = [snet for snet in G.neighbors(next_node) if  G.get_edge_data( next_node, snet)['weight']&~8 == 4]
                            gate_net =  [gnet for gnet in G.neighbors(next_node) if  G.get_edge_data( next_node, gnet)['weight'] == 2]
                            logger.debug(f"neighbor gate: {gate_net} source:{source_net},all neighbors: {list(G.edges(node,data=True))} {len(common_nets)}")
                            if len(gate_net)==len(source_net)==1:
                                source_net=source_net[0]
                                gate_net=gate_net[0]
                                logger.debug(f"source net: {source_net}, gate net: {gate_net}")
                            else:
                                continue

                            if gate_net in G.neighbors(node) \
                                and G.get_edge_data( node, gate_net)['weight'] == 2 \
                                    and len(common_nets)>2:
                                logger.debug(f"source net: {source_net}, gate net: {gate_net}")
                            else:
                                continue
                            logger.debug(f"check stack transistors: {node}, {next_node}, {gate_net}, {source_net},{common_nets}")
                            if G.nodes[net]["net_type"]!="external" :
                                if G.get_edge_data( node, gate_net)['weight'] >= 2 :
                                    logger.debug(f"checking values {G.nodes[next_node]},{G.nodes[next_node]}")
                                    if 'stack' in G.nodes[next_node]["values"]:
                                        stack=G.nodes[next_node]["values"].pop("stack")
                                    else:
                                        stack=1
                                    if 'stack' in G.nodes[node]["values"]:
                                        stack=stack+G.nodes[node]["values"].pop("stack")
                                    else:
                                        stack =stack+1
                                    if G.nodes[next_node]["values"]==G.nodes[node]["values"]:
                                        modified_nodes[node] = stack
                                    remove_nodes.append(net)
                                    if G.has_edge(node,source_net):
                                        wt= G[next_node][source_net]["weight"] | G[node][source_net]["weight"]
                                    else:
                                         wt= G[next_node][source_net]["weight"]
                                    modified_edges[node] = [ source_net, wt ]
                                    logger.debug(f"successfully modified node {modified_nodes}")
                                    remove_nodes.append(next_node)
    for node, attr in modified_edges.items():
        #Change source connection and port name
        G.add_edge(node, attr[0], weight=attr[1])
        logger.debug(f"updating port names{G.nodes[node]['ports']} with {attr}")
        G.nodes[node]["ports"][2]=attr[0]

    for node, attr in modified_nodes.items():
        G.nodes[node]["values"]['stack'] = attr

    for node in remove_nodes:
        G.remove_node(node)
    for node, attr in modified_nodes.items():
        wt=[G.get_edge_data(node, net)['weight'] for net in G.neighbors(node)]
        logger.debug(f"new neighbors of {node} {G.nodes[node]} {list(G.neighbors(node))} {wt}")

    logger.debug(f"reduced_size after resolving stacked transistor: {len(G)} {G.nodes()}")
    logger.debug(
        "\n######################START CREATING HIERARCHY##########################\n"
    )
