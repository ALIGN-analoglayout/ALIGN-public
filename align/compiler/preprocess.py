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
# from .merge_nodes import convert_unit
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
                    print("parameter type",y.model, type(ele.parameters), y.parameters)
                    y.parameters.update({k : v for k,v in y.parameters.items() if k in ele.parameters})
                    logger.info(f"new instance parameters: {y.parameters}")
                    other_ckt.elements.append(Instance(
                        name = ele.name.replace('X',library.find(y.model).prefix),
                        model = y.model,
                        pins = pins,
                        parameters = y.parameters,
                        abstract_name = y.abstract_name,
                        generator = y.generator
                        ))
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
    logger.debug(f"merging all stacked/series devices, initial ckt size: {len(ckt.elements)}")
    remove_nodes = []
    for net in set(ckt.nets)-set(ckt.pins):
        G = Graph(ckt)
        nbrs = sorted(list(G.neighbors(net)))
        if len(nbrs)==2 and net not in remove_nodes:
            nbr1,nbr2 = [ckt.get_element(nbr) for nbr in nbrs]
            #Same instance type
            if nbr1.model !=nbr2.model:
                continue
            #Valid only for Single pin connection e.g, set(D,S) or (+,-)
            if len(G.get_edge_data(nbr1.name, net)['pin']) !=1 or \
                len(G.get_edge_data(nbr2.name, net)['pin']) !=1:
                continue
            # Filter (D,D) or (S,S) or (G,G) connection
            if G.get_edge_data(nbr1.name, net)['pin'] == G.get_edge_data(nbr2.name, net)['pin']:
                continue
            logger.debug(f" conn1: {G.get_edge_data(nbr1.name, net)['pin']}, conn2: {G.get_edge_data(nbr2.name, net)['pin']}")
            connections = set([list(G.get_edge_data(nbr, net)['pin'])[0] for nbr in nbrs])
            logger.debug(f"connection with neighbors: {connections}")
            assert len(connections) ==2, f"Not a stack {nbrs} as connections: {connections} are not allowed"
            nbr1p = dict(**nbr1.parameters,**nbr1.pins)
            nbr2p = dict(**nbr2.parameters,**nbr2.pins)
            stack1 = int(nbr1p.pop('STACK',1))
            stack2 = int(nbr2p.pop('STACK',1))
            for connection in connections:
                assert connection in nbr1p, f"pin {connection} not found in {nbr1p}"
                assert connection in nbr2p, f"pin {connection} not found in {nbr2p}"
                del nbr1p[connection]
                del nbr2p[connection]

            if nbr1p == nbr2p and connections in [set(['D','S']),set(['PLUS','MINUS'])]:
                logger.warning(f"stacking {nbrs} {stack1 + stack2}")
                nbr1.parameters['STACK'] = stack1 +stack2
                for p,n in nbr1.pins.items():
                    if net ==n:
                        nbr1.pins[p]=nbr2.pins[p]
                G.remove(nbr2)


