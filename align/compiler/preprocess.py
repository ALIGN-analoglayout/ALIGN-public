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
    design_setup['KEEP_DUMMY'] = False
    design_setup['SERIES'] = True
    design_setup['PARALLEL'] = True
    top = ckt_data.find(design_name)
    if top.name not in design_setup['DIGITAL']:
        define_SD(top, design_setup['POWER'], design_setup['GND'], design_setup['DIGITAL'])

    for subckt in ckt_data:
        if isinstance(subckt, SubCircuit):
            logger.debug(f"Preprocessing stack/parallel circuit name: {subckt.name}")
            if subckt.name not in design_setup['DIGITAL']:
                logger.debug(f"Starting no of elements in subckt {subckt.name}: {len(subckt.elements)}")
                if 'PARALLEL' in design_setup:
                    #Find parallel devices and add a parameter parallel to them, all other parameters should be equal
                    add_parallel_devices(subckt, design_setup['PARALLEL'])
                if 'SERIES' in design_setup:
                    #Find parallel devices and add a parameter parallel to them, all other parameters should be equal
                    add_series_devices(subckt, design_setup['SERIES'])
                logger.debug(f"After reducing series/parallel, elements count in subckt {subckt.name}: {len(subckt.elements)}")

    if isinstance(top, SubCircuit):
        if top.name not in design_setup['DIGITAL']:
            if 'KEEP_DUMMY' in design_setup:
                #remove single instance subcircuits
                dummy_hiers = []
                find_dummy_hier(ckt_data, top, dummy_hiers, design_setup['KEEP_DUMMY'])
                if len(dummy_hiers)>0:
                    logger.info(f"Removing dummy hierarchies {dummy_hiers}")
                    remove_dummies(ckt_data, dummy_hiers, top.name)

def remove_dummies(library, dummy_hiers, top):
    for h in dummy_hiers:
        if h==top:
            logger.debug("Cant delete top hierarchy {top}")
            return
        ckt = library.find(h)
        assert ckt
        with set_context(library):
            logger.info(f"Flattening dummy hierarchy {ckt.name}")
            for other_ckt in library:
                if isinstance(other_ckt, SubCircuit) and not other_ckt.name == ckt.name:
                    replace = {}
                    for inst in other_ckt.elements:
                        if inst.model == ckt.name:
                            logger.debug(f"removing instance {inst} with instance {ckt.elements[0].model}")
                            replace[inst.name] = ckt.elements[0]
                            #@Parijat, is there a better way to modify?
                    with set_context(other_ckt.elements):
                        for x,y in replace.items():
                            ele = other_ckt.get_element(x)
                            assert ele
                            pins = {}
                            for p,v in y.pins.items():
                                pins[p] = ele.pins[v]
                            y.parameters.update({k : v for k,v in ele.parameters.items() if k in y.parameters})
                            logger.debug(f"new instance parameters: {y.parameters}")
                            _prefix= library.find(y.model).prefix
                            if not _prefix:
                                _prefix = 'M' #default value, used in testing
                            other_ckt.elements.append(Instance(
                                name = ele.name.replace('X',_prefix),
                                model = y.model,
                                pins = pins,
                                parameters = y.parameters,
                                generator = y.generator
                                ))
                            other_ckt.elements.remove(ele)
            logger.info(f'Removing hierarchy {h}')
            library.remove(ckt)
            assert library.find(h) == None

def find_dummy_hier(library, ckt, dummy_hiers, update=False):
    if update == True:
        return
    assert isinstance(dummy_hiers, list)
    all_subckts = [str(e.model) for e in ckt.elements if isinstance(library.find(e.model), SubCircuit)]
    logger.info(f"Checking hiearchy {ckt.name} subckts {all_subckts} filter: {dummy_hiers}")
    for m in set(all_subckts)-set(dummy_hiers):
        find_dummy_hier(library, library.find(m), dummy_hiers)
    if len(ckt.elements) ==1:
        dummy_hiers.append(ckt.name)



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

def define_SD(circuit,power,gnd,digital=None):
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

    if digital and circuit.name in digital:
        return
    if not power or not gnd:
        logger.warning(f"No power and gnd in this circuit {circuit.name}, please check setup file")
        return

    G = Graph(circuit)
    ports = circuit.pins
    high = []
    low = []
    if power and gnd:
        high= list(set(power).intersection(set(ports)))
        low = list(set(gnd).intersection(set(ports)))
        logger.debug(f"Using power: {high} and ground: {low}")
    assert high, f"VDD port {power} not defined in subckt port {circuit.pins}"
    assert low, f"GND port {gnd} not defined in subckt port {circuit.pins}"

    logger.debug(f"START checking source and drain in graph ")

    probable_changes_p = []
    assert high[0] in circuit.nets
    traversed = high.copy()
    traversed.extend(gnd)
    while high:
        nxt = high.pop(0)
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

    for inst in circuit.elements:
        inst_ckt = circuit.parent.find(inst.model)
        if isinstance(inst_ckt, SubCircuit):
            pp = [p for p,c in inst.pins.items() if c in power]
            gp = [p for p,c in inst.pins.items() if c in gnd]
            define_SD(inst_ckt, pp, gp, digital)

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
    logger.debug(f"Checking parallel devices in {ckt.name}, initial ckt size: {len(ckt.elements)}")

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
    logger.debug(f"Checking stacked/series devices, initial ckt size: {len(ckt.elements)}")
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
            connections = set([list(G.get_edge_data(nbr, net)['pin'])[0] for nbr in nbrs])
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
                logger.info(f"stacking {nbrs} {stack1 + stack2}")
                nbr1.parameters['STACK'] = stack1 +stack2
                for p,n in nbr1.pins.items():
                    if net ==n:
                        nbr1.pins[p]=nbr2.pins[p]
                G.remove(nbr2)


