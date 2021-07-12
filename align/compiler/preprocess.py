#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Thu Sep 17 15:49:33 2020

@author: kunal001
"""

from os import replace
from align.schema.types import set_context
from align.schema import model
from align.schema.subcircuit import Circuit,SubCircuit
from .merge_nodes import convert_unit
from .util import get_next_level, get_base_model
from ..schema.graph import Graph
from ..schema.visitor import Transformer
import logging
import networkx as nx
import copy
from align.schema.instance import Instance

logger = logging.getLogger(__name__)



def preprocess_stack_parallel(ckt_data, design_setup, design_name):
    """
    Preprocess the input graph by reducing parallel device, series devices, remove dummy hierarchies.
    removes power pins to be sent as signal by recursively finding all connections to power pins
    and removing them from subcircuit definition and instance calls
    for each circuit different power connection creates an extra subcircuit
    Required by PnR as it does not make power connections as ports
    """
    remove_dummy = []
    design_setup['KEEP_DUMMY'] = False
    design_setup['SERIES'] = True
    design_setup['PARALLEL'] = True
    for subckt in ckt_data:
        if isinstance(subckt, SubCircuit):
            logger.debug(f"preprocessing circuit name: {subckt}")
            if subckt.name not in design_setup['DIGITAL']:
                define_SD(subckt,design_setup['POWER'],design_setup['GND'], design_setup['CLOCK'])
                logger.debug(f"Starting no of elements in subckt {subckt.name}: {len(subckt.elements)}")
                if 'PARALLEL' in design_setup and design_setup['PARALLEL'] == True:
                    #Find parallel devices and add a parameter parallel to them, all other parameters should be equal
                    add_parallel_devices(subckt,True)
                if 'SERIES' in design_setup and design_setup['SERIES'] == True:
                    #Find parallel devices and add a parameter parallel to them, all other parameters should be equal
                    add_series_devices(subckt,True)
                if 'KEEP_DUMMY' in design_setup \
                    and design_setup['KEEP_DUMMY'] == False\
                    and not subckt.name == design_name:
                    #remove single instance subcircuits
                    if remove_dummy_hier(ckt_data,subckt,True):
                        remove_dummy.append(subckt.name)
                logger.debug(f"After preprocessing no of elements in subckt {subckt.name}: {len(subckt.elements)}")

    if len(remove_dummy) >0:
        logger.info(f"Removing dummy hierarchies {remove_dummy}")
    with set_context(ckt_data):
        for ckt in remove_dummy:
            ckt_data.remove(ckt_data.find(ckt))
            assert ckt_data.find(ckt) == None

def remove_dummy_hier(library,ckt,update=True):
    if update == True and not len(ckt.elements) ==1:
        return False
    if  library.find(ckt.elements[0].model) and isinstance(library.find(ckt.elements[0].model), SubCircuit):
        remove_dummy_hier(library,library.find(ckt.elements[0].model))
    for other_ckt in library:
        if isinstance(other_ckt, SubCircuit):
            G = Graph(other_ckt)
            replace = {}
            for inst in other_ckt.elements:
                if inst.model == ckt.name:
                    logger.info(f"removing instance {inst} with instance {ckt.elements[0].model}")
                    replace[inst.name] = ckt.elements[0]
                    #@Parijat, is there a better way to modify?
            with set_context(other_ckt.elements):
                for x,y in replace.items():
                    ele = other_ckt.get_element(x)
                    assert ele
                    pins = {}
                    for p,v in y.pins.items():
                        pins[p] = ele.pins[v]
                    assert ele.parameters.keys() & y.parameters.keys(), \
                        f"cannot remove dummy hierarchy {ele.model}, as parameters cannot be propogated"
                    logger.debug(y.parameters, ele.parameters)
                    other_ckt.elements.append(Instance(
                        name = ele.name.replace('X','M'),
                        model = y.model,
                        pins = pins,
                        parameters={**y.parameters, **ele.parameters}))
                    other_ckt.elements.remove(ele)
    return True


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
    G = Graph(circuit)
    ports = circuit.pins
    high = []
    low = []
    if power and gnd:
        high= list(set(power).intersection(set(ports)))
        low = list(set(gnd).intersection(set(ports)))
        logger.debug(f"Using power: {high} and ground: {low}")
    if not high or not low:
        logger.warning(f'No power and gnd in this circuit {circuit.name}')
        return
    logger.debug(f"START checking source and drain in graph ")

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
                logger.info(f"removing parallel nodes {pd}")
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
        if len(nbrs)==2 and net not in remove_nodes:
            nbr1,nbr2 = [ckt.get_element(nbr) for nbr in nbrs]
            connections = set([list(G.get_edge_data(nbr, net)['pin'])[0] for nbr in nbrs])
            nbr1p = dict({'MODEL':nbr1.model},**nbr1.parameters,**nbr1.pins)
            nbr2p = dict({'MODEL':nbr2.model},**nbr2.parameters,**nbr2.pins)
            stack1 = int(nbr1p.pop('STACK',1))
            stack2 = int(nbr2p.pop('STACK',1))
            for connection in connections:
                del nbr1p[connection[0]]
                del nbr2p[connection[0]]

            if nbr1p == nbr2p and connections in [set(['D','S']),set(['+','-'])]:
                logger.warning(f"stacking {nbrs} {stack1 + stack2}")
                nbr1.parameters['STACK'] = stack1 +stack2
                for p,n in nbr1.pins.items():
                    if net ==n:
                        nbr1.pins[p]=nbr2.pins[p]
                G.remove(nbr2)

# def remove_pg_pins(ckt_data:dict,circuit_name, pg_pins):
#     """
#     removes power pins to be sent as signal by recursively finding all connections to power pins
#     and removing them from subcircuit defination and instance calls
#     for each circuit different power connection creates an extra subcircuit
#     Required by PnR as it does not make power connections as ports
#     Parameters
#     ----------
#     ckt_data : dict
#         dictionary of all circuit in spice file
#     circuit_name : str
#         name of circuit to be processed.
#     G : networkx graph
#         graph of circuit.
#     pg_pins : list
#         graph of circuit.
#     Returns
#     -------
#     None.

#     """
#     G = ckt_data[circuit_name]["graph"]
#     logger.debug(f"checking pg ports in {circuit_name} {pg_pins}")
#     for node, attr in G.nodes(data=True):
#         if 'sub_graph' not in attr or attr['inst_type'] =='net' or not attr["connection"]:
#             continue
#         elif len(set(attr["connection"].values()) & set(pg_pins))>0:
#             logger.debug(f"node: {node} connections {attr['connection']} {attr['ports']}")
#             pg_conn = {}
#             for k,v in attr["connection"].items():
#                 if v in pg_pins and k not in pg_pins:
#                     pg_conn[k]=v
#             if pg_conn:
#                 logger.debug(f"removing power pin connected as signal net {pg_conn} in {node}")
#                 #deleting power connections to subcircuits
#                 for k,v in pg_conn.items():
#                     del attr["connection"][k]
#                     del attr['edge_weight'][attr["ports"].index(v)]
#                     attr["ports"].remove(v)
#                 #create a new subcircuit and changes its ports to power ports
#                 #power ports are not written during verilog
#                 updated_name = modify_pg_conn_subckt(ckt_data,attr["inst_type"], pg_conn)
#                 attr["instance"].model = updated_name
#                 remove_pg_pins(ckt_data,updated_name, pg_pins)

# def modify_pg_conn_subckt(ckt_data:dict,circuit_name, pg_conn):
#     """
#     creates a new subcircuit by removing power pins from a subcircuit defination
#     and change internal connections within the subcircuit

#     Parameters
#     ----------
#     ckt_data : dict
#         dictionary of all circuit in spice file
#     circuit_name : str
#         name of circuit to be processed.
#     pg_conn : dict
#         ports to be modified and corresponding pg pin.
#     Returns
#     -------
#     new subcircuit name

#     """

#     new = copy.deepcopy(ckt_data[circuit_name])
#     logger.debug(f"modifying subckt {circuit_name} {new} {pg_conn}")
#     for k,v in pg_conn.items():
#         logger.debug(f"fixing port {k} to {v} for all inst in {circuit_name}")
#         new["ports"].remove(k)
#         del new["ports_weight"][k]
#         if v in new["graph"].nodes():
#             old_edge_wt=list(copy.deepcopy(new["graph"].edges(v,data=True)))
#             new["graph"] = nx.relabel_nodes(new["graph"],{k:v},copy=False)
#             for n1,n2,v1 in new["graph"].edges(v,data=True):
#                 for n11,n21,v11 in old_edge_wt:
#                     if n1 == n11 and n2 ==n21:
#                         v1["weight"] = v1["weight"] | v11["weight"]
#             logger.debug(f"updated weights {old_edge_wt} {new['graph'].edges(v,data=True)}")

#         else:
#             new["graph"] = nx.relabel_nodes(new["graph"],{k:v},copy=False)

#         for node,attr in new["graph"].nodes(data=True):
#             if attr["instance"].model=='net':
#                 continue
#             #if k in attr["ports"]:
#             #logger.debug(f"updating node {node} {attr}")
#             attr["ports"]=[v if x==k else x for x in attr["ports"]]
#             if "connection" in attr and attr["connection"]:
#                 for a,b in attr["connection"].items():
#                     if b==k:
#                         attr["connection"][a]=v
#                         logger.debug(f"updated attributes of {node}: {attr}")

#     i=1
#     updated_ckt_name = circuit_name+'pg'+str(i)
#     while updated_ckt_name in ckt_data.keys():
#         if ckt_data[updated_ckt_name]["ports"]==new["ports"]:
#             break
#         else:
#             i = i+1
#             updated_ckt_name = circuit_name+'pg'+str(i)
#     ckt_data[ updated_ckt_name] = new
#     return updated_ckt_name
