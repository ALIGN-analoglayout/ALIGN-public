#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Sep 17 15:49:33 2020

@author: kunal001
"""

from align.schema import model
from align.schema.subcircuit import Circuit
from .merge_nodes import convert_unit
from .util import get_next_level, get_base_model
from ..schema.graph import Graph

import logging
import networkx as nx
import copy

logger = logging.getLogger(__name__)

def remove_pg_pins(ckt_data:dict,circuit_name, pg_pins):
    """
    removes power pins to be sent as signal by recursively finding all connections to power pins
    and removing them from subcircuit defination and instance calls
    for each circuit different power connection creates an extra subcircuit
    Required by PnR as it does not make power connections as ports
    Parameters
    ----------
    ckt_data : dict
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
    G = ckt_data[circuit_name]["graph"]
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
                updated_name = modify_pg_conn_subckt(ckt_data,attr["inst_type"], pg_conn)
                attr["instance"].model = updated_name
                remove_pg_pins(ckt_data,updated_name, pg_pins)

def modify_pg_conn_subckt(ckt_data:dict,circuit_name, pg_conn):
    """
    creates a new subcircuit by removing power pins from a subcircuit defination
    and change internal connections within the subcircuit

    Parameters
    ----------
    ckt_data : dict
        dictionary of all circuit in spice file
    circuit_name : str
        name of circuit to be processed.
    pg_conn : dict
        ports to be modified and corresponding pg pin.
    Returns
    -------
    new subcircuit name

    """

    new = copy.deepcopy(ckt_data[circuit_name])
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
            if attr["instance"].model=='net':
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
    while updated_ckt_name in ckt_data.keys():
        if ckt_data[updated_ckt_name]["ports"]==new["ports"]:
            break
        else:
            i = i+1
            updated_ckt_name = circuit_name+'pg'+str(i)
    ckt_data[ updated_ckt_name] = new
    return updated_ckt_name


def preprocess_stack_parallel(ckt_data:dict,circuit_name):
    """
    Preprocess the input graph by reducing parallel caps, series resistance, identify stacking, adding parallel transistors.

    Parameters
    ----------
    ckt_data : dict
        dictionary of all circuit in spice file
    circuit_name : str
        name of circuit to be processed.
    G : networkx graph
        graph of circuit.

    Returns
    -------
    None.

    """
    ckt = ckt_data.find(circuit_name)
    logger.debug(f"no of nodes: {len(ckt.elements)}")
    add_parallel_caps(ckt,update=True)
    add_series_res(ckt)
    add_stacked_transistor(ckt)
    add_parallel_transistor(ckt)
    initial_size=len(ckt.elements)
    delta =1
    while delta > 0:
        logger.debug(f"CHECKING stacked transistors {circuit_name} {ckt.elements}")
        add_stacked_transistor(ckt_data)
        add_parallel_transistor(ckt_data)
        delta = initial_size - len(ckt.elements)
        initial_size = len(ckt.elements)
    #remove single instance subcircuits
    subckt = ckt_data.find(circuit_name)
    if len(subckt.elements)==1:
        #Check any existing hier
        print(subckt.elements[0])
        if 'sub_graph' in subckt.elements[0].keys() and subckt.elements[0]['sub_graph'] is not None:
            logger.debug(f"sub_graph nodes {attributes[0]['sub_graph'].nodes()}")
            stacked_ckt = preprocess_stack_parallel(ckt_data,attributes[0]["real_inst_type"],attributes[0]["sub_graph"])
            if stacked_ckt ==None:
                return None

        for ckt in ckt_data.values():
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


def swap_SD(circuit,G,node):
    """change_SD
    swap source drain nets of transistor]

    Args:
        circuit ([type]): [description]
        G ([type]): [description]
        node ([type]): [description]
    """
    for nbr in G.neighbors(node):
        if 'D' in G.get_edge_data(node, nbr)['pin']:
            nbrd = nbr
        elif 'S' in G.get_edge_data(node, nbr)['pin']:
            nbrs = nbr
    assert nbrs and nbrd
    #Swapping D and S
    logger.warning(f"Swapping D and S {node} {nbrd} {nbrs} {circuit.get_element(node)}")
    circuit.get_element(node).pins.update({'D':nbrs,'S':nbrd})

def define_SD(circuit,power,gnd,update=True):
    """define_SD
    Checks for scenarios where transistors D/S are flipped.
    It is valid configuration in spice as transistors D and S are invertible
    During subcircuit identification it becomes tricky as it requires multiple building blocks in the library
    One with normal connection and one with flipped connections
    Here, we traverses the circuit from power net to gnd and check
    1. PMOS 'S' pin at high potential (comes first in traversal)
    2. NMOS 'D' pin at high potential (comes first in traversal)
    Next check for Transmission gate like structures where both cases:
    We do another traversal from gnd net to power net and take a intersection of nodes to flip

    Args:
        circuit ([type]): [description]
        power ([type]): [description]
        gnd ([type]): [description]
        clk ([type]): [description]
    """
    if update ==False:
        return
    logger.debug(f"START checking source and drain in graph ")
    G = Graph(circuit)
    ports = circuit.pins
    if power and gnd:
        assert set(power) & set(ports), f"Power net {power} is not in the list of ports {ports} of {circuit.name}"
        assert set(gnd) & set(ports), f"Gnd net {power} is not in the list of ports {ports} of {circuit.name}"
        high= list(set(power).intersection(set(ports)))
        low = list(set(gnd).intersection(set(ports)))
        logger.debug(f"Using power: {high} and ground: {low}")

    if not high or not low:
        logger.warning(f'No power and gnd in this circuit {circuit.name}')
        return
    probable_changes_p = []
    assert high[0] in circuit.nets
    traversed = high.copy()
    traversed.extend(gnd)
    while high:
        nxt = high.pop(0)
        for node in get_next_level(circuit,G,[nxt]):
            logger.debug(f"VDD:checking node: {node}, {high}, {traversed}")
            edge_type = G.get_edge_data(node, nxt)['pin']
            if not set(edge_type)-set({'G'}) or node in traversed:
                continue
            if circuit.get_element(node):
                base_model = get_base_model(circuit,node)
            else:
                assert node in circuit.nets
                base_model = "net"
            if 'PMOS' == base_model:
                if 'D' in edge_type :
                    probable_changes_p.append(node)
            elif 'NMOS' == base_model:
                if 'S' in edge_type :
                    probable_changes_p.append(node)
            high.append(node)
            traversed.append(node)
        print("high",high)
    if len(probable_changes_p)==0:
        return
    probable_changes_n=[]
    traversed = low.copy()
    traversed.extend(list(set(power).intersection(set(ports))))
    while low:
        nxt = low.pop(0)
        for node in get_next_level(circuit,G,[nxt]):
            edge_type = G.get_edge_data(node, nxt)['pin']
            if not set(edge_type)-set({'G'}) or node in traversed:
                continue
            if circuit.get_element(node):
                base_model = get_base_model(circuit,node)
            else:
                assert node in circuit.nets
                base_model = "net"
            if 'PMOS' == base_model:
                if 'S' in edge_type :
                    probable_changes_n.append(node)
            elif 'NMOS' == base_model:
                if 'D' in edge_type :
                    probable_changes_n.append(node)
            low.append(node)
            traversed.append(node)

    for node in list (set(probable_changes_n) & set(probable_changes_p)):
        logger.warning(f"changing source drain: {node}")
        swap_SD(circuit,G,node)


def add_parallel_devices(ckt,update=True):
    """add_parallel_devics
        merge devices in parallel as single unit
        Keeps 1st device out of sorted list
        #TODO Optimize later
    Args:
        ckt ([type]): [description]
        update (bool, optional): [description]. Defaults to True.
    """
    if update == False:
        return
    logger.debug(f"merging all parallel devices, initial ckt size: {len(ckt.elements)}")

    for net in set(ckt.nets):
        pp_list = []
        parallel_devices={}
        G = Graph(ckt)
        for node in G.neighbors(net):
            logger.warning(f"checking node {node} {net}")
            ele = ckt.get_element(node)
            p = {**ele.pins, **ele.parameters}
            p['model'] = ele.model
            if p in pp_list:
                parallel_devices[pp_list.index(p)].append(node)
            else:
                pp_list.append(p)
                parallel_devices[pp_list.index(p)] = [node]
        for pd in parallel_devices.values():
            if len(pd)> 1:
                logger.warning(f"removing parallel nodes {pd}")
                pd0 = sorted(pd)[0]
                ckt.get_element(pd0).parameters['PARALLEL']=len(set(pd))
                for rn in pd[1:]:
                    G.remove_node(rn)

def add_series_devices(ckt,update=True):
    """add_parallel_devics
        merge devices in parallel as single unit
        Keeps 1st device out of sorted list
        #TODO Optimize later
    Args:
        ckt ([type]): [description]
        update (bool, optional): [description]. Defaults to True.
    """
    if update == False:
        return
    logger.debug(f"merging all caps, initial ckt size: {len(ckt.elements)}")
    remove_nodes = []
    for net in set(ckt.nets)-set(ckt.pins):
        G = Graph(ckt)
        nbrs = sorted(list(G.neighbors(net)))
        logger.warning(f"net {net} {nbrs}")
        if len(nbrs)==2 and net not in remove_nodes:
            nbr1,nbr2 = [ckt.get_element(nbr) for nbr in nbrs]
            connections = set([list(G.get_edge_data(nbr, net)['pin'])[0] for nbr in nbrs])
            nbr1p = dict({'MODEL':nbr1.model},**nbr1.parameters,**nbr1.pins)
            nbr2p = dict({'MODEL':nbr2.model},**nbr2.parameters,**nbr2.pins)
            stack1 = nbr1p.pop('STACK',1)
            stack2 = nbr2p.pop('STACK',1)
            for connection in connections:
                del nbr1p[connection[0]]
                del nbr2p[connection[0]]

            logger.warning(f"{nbr1p} {nbr2p}")
            if nbr1p == nbr2p and connections in [set(['D','S']),set(['+','-'])]:
                logger.warning(f"stacking {nbrs}")
                nbr1.parameters['STACK'] = stack1 +stack2
                for p,n in nbr1.pins.items():
                    if net ==n:
                        nbr1.pins[p]=nbr2.pins[p]
                ckt.remove(nbr2)
                remove_nodes.append(nbrs[1])
    # for ele in remove_nodes:
