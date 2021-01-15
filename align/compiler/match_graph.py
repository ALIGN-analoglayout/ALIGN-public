# -*- coding: utf-8 -*-
"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""
#%%
import os
import networkx as nx
from networkx.algorithms import isomorphism

from .merge_nodes import merge_nodes, merged_value
from .util import get_next_level
from .write_constraint import FindSymmetry

import pprint
import logging
logger = logging.getLogger(__name__)


#%%

class Annotate:
    def __init__(self,hier_graph_dict,design_setup,library,existing_generator):
        self.updated_ckt_list = []
        self.hier_graph_dict = hier_graph_dict
        self.duplicates={}
        self.digital=design_setup['DIGITAL']
        self.pg = design_setup['POWER']+design_setup['GND']
        self.lib = library
        self.clk = design_setup['CLOCK']
        self.all_lef = existing_generator
        self.stop_points = self.pg+self.clk
        
    def annotate(self):   
        for circuit_name, circuit in self.hier_graph_dict.items():
            logger.debug(f"START MATCHING in circuit: {circuit_name}")
            G1 = circuit["graph"]
            if circuit_name in self.digital:
                mapped_graph_list = self._mapped_graph_list(G1,  self.pg ,self.clk, True )
            else:
                mapped_graph_list = self._mapped_graph_list(G1, self.pg ,self.clk, False )
            # reduce graph converts input hierarhical graph to dictionary
            updated_circuit, Grest = self._reduce_graph(G1, mapped_graph_list)
            check_nodes(updated_circuit)
            self.updated_ckt_list.extend(updated_circuit)
    
            if circuit_name not in self.digital:
                symmetry_blocks = FindSymmetry(Grest, circuit["ports"], circuit["ports_weight"], self.stop_points)
                for symm_blocks in symmetry_blocks.values():
                    logger.info(f"generated constraints: {pprint.pformat(symm_blocks, indent=4)}")
                    if isinstance(symm_blocks, dict) and "graph" in symm_blocks.keys():
                        logger.debug(f"added new hierarchy: {symm_blocks['name']} {symm_blocks['graph'].nodes()}")
                        self.updated_ckt_list.append(symm_blocks)
    
            self.updated_ckt_list.append({
                "name": circuit_name,
                "graph": Grest,
                "ports": circuit["ports"],
                "ports_weight": circuit["ports_weight"],
                "size": len(Grest.nodes())
            })
    
            self.lib_names=[lib_ele['name'] for lib_ele in self.lib]
            for lib_name, dupl in self.duplicates.items():
                if len(dupl)>1:
                    self.lib_names+=[lib_name+'_type'+str(n) for n in range(len(dupl))]
        return self.updated_ckt_list, self.lib_names
    def _reduce_graph(self,circuit_graph, mapped_graph_list):
        """
        merge matched graphs
        """
        logger.debug("START reducing graph: ")
        G1 = circuit_graph.copy()
        updated_circuit = []
        for lib_ele in self.lib:
            sub_block_name = lib_ele['name']
            if sub_block_name in mapped_graph_list:
                logger.debug(f"Reducing ISOMORPHIC sub_block: {sub_block_name}{mapped_graph_list[sub_block_name]}")
    
                for Gsub in sorted(mapped_graph_list[sub_block_name], key= lambda i: '_'.join(sorted(i.keys()))):
                    G2 = lib_ele['graph'].copy()
                    logger.debug(f"nodes in library graph {G2.nodes()}")
    
                    if already_merged(G1,Gsub):
                        continue
                    remove_these_nodes = [
                        key for key in Gsub
                        if 'net' not in G1.nodes[key]["inst_type"]]
                    logger.debug(f"Reduce nodes: {', '.join(remove_these_nodes)}")
                    if sub_block_name in self.all_lef:
                        pg = []
                    else:
                        pg = self.pg
                    matched_ports,ports_weight = copy_matched_subcircuit_attributes(G1,G2,Gsub,lib_ele['ports'],len(remove_these_nodes),pg)
    
                    if len(remove_these_nodes) == 1:
                        logger.debug(f"One node element: {sub_block_name}")
                        G1.nodes[remove_these_nodes[0]]["inst_type"] = sub_block_name
                        G1.nodes[remove_these_nodes[0]]["ports_match"] = matched_ports
                        updated_values = merged_value({}, G1.nodes[remove_these_nodes[0]]["values"])
                        G1.nodes[remove_these_nodes[0]]["values"] = updated_values
    
                    else:
                        logger.debug(f"Multi node element: {sub_block_name} {matched_ports}")
                        _, subgraph,new_node = merge_nodes(
                            G1, sub_block_name, remove_these_nodes, matched_ports)
                        if sub_block_name not in self.all_lef:
                            logger.debug(f'Calling recursive for block: {sub_block_name}')
                            mapped_subgraph_list = self._mapped_graph_list(
                                G2, [
                                    i for i in self.lib
                                    if not (i['name'] == sub_block_name)
                                ])
                            logger.debug("Recursive calling to find sub_sub_ckt")
                            updated_subgraph_circuit, Grest = self._reduce_graph(
                                G2, mapped_subgraph_list)
    
                            updated_circuit.extend(updated_subgraph_circuit)
                        else:
                            Grest = subgraph
    
                        logger.debug(f"adding new sub_ckt: {sub_block_name} {self.duplicates.keys()}")
                        check_nodes(updated_circuit)
                        update_name = multiple_instances(G1,new_node,sub_block_name,self.duplicates)
    
                        super_node = {
                                "name": update_name,
                                "graph": Grest,
                                "ports": list(matched_ports.keys()),
                                "ports_match": matched_ports,
                                "ports_weight": ports_weight,
                                "size": len(subgraph.nodes())
                            }
                        updated_circuit.append(super_node)
    
                        check_nodes(updated_circuit)
        logger.debug(f"Finished one branch: {sub_block_name}")
        return updated_circuit, G1
    def _mapped_graph_list(self,G1, POWER=None,CLOCK=None, DIGITAL=False):
        """
        find all matches of library element in the graph
        """
    
        logger.debug(f"Matching circuit Graph from library elements {G1.nodes} {G1.edges(data=True)}")
        mapped_graph_list = {}
    
        for lib_ele in self.lib:
            G2 = lib_ele['graph']
            # Digital blocks only transistors:
            nd = [node for node in G2.nodes()
                    if 'net' not in G2.nodes[node]["inst_type"]]
            if DIGITAL and len(nd)>1:
                continue
    
            sub_block_name = lib_ele['name']
            if len(G2.nodes)<=len(G1.nodes):
                logger.debug(f"Matching: {sub_block_name} : {G2.nodes} {G2.edges(data=True)}")
            GM = isomorphism.GraphMatcher(
                G1, G2,
                node_match=isomorphism.categorical_node_match(['inst_type'],
                                                              ['nmos']),
                edge_match=isomorphism.categorical_edge_match(['weight'], [1]))
    
            if GM.subgraph_is_isomorphic():
                logger.debug(f"ISOMORPHIC : {sub_block_name}")
                map_list = []
    
                for Gsub in GM.subgraph_isomorphisms_iter():
    
                    all_nd = [key for key in Gsub.keys() if 'net' not in G1.nodes[key]["inst_type"]]
                    logger.debug(f"matched inst: {all_nd}")
                    if len(all_nd)>1 and dont_touch_clk(Gsub,CLOCK):
                        logger.debug("Discarding match due to clock")
                        continue
                    if sub_block_name.startswith('DP')  or sub_block_name.startswith('CMC'):
                        if G1.nodes[all_nd[0]]['values'] == G1.nodes[all_nd[1]]['values'] and \
                            compare_balanced_tree(G1,get_key(Gsub,'DA'),get_key(Gsub,'DB'),[all_nd[0]],[all_nd[1]]) :
                            if 'SA' in Gsub.values() and \
                            compare_balanced_tree(G1,get_key(Gsub,'SA'),get_key(Gsub,'SB'),[all_nd[0]],[all_nd[1]]):
                                map_list.append(Gsub)
                                logger.debug(f"Matched Lib: {' '.join(Gsub.values())}")
                                logger.debug(f"Matched Circuit: {' '.join(Gsub)}")
                            # remove pseudo diff pair
                            elif sub_block_name.startswith('DP') and POWER is not None and get_key(Gsub,'S') in POWER:
                                logger.debug(f"skipping pseudo DP {POWER}: {' '.join(Gsub)}")
                            else:
                                map_list.append(Gsub)
                                logger.debug(f"Matched Lib: {' '.join(Gsub.values())}")
                                logger.debug(f"Matched Circuit: {' '.join(Gsub)} power:{POWER}")
                        else:
                            logger.debug(f"Discarding match {sub_block_name}, {G1.nodes[all_nd[0]]['values']}, {G1.nodes[all_nd[1]]['values']}")
                    elif sub_block_name.startswith('SCM') and G1.nodes[all_nd[0]]['values'] != G1.nodes[all_nd[1]]['values']:
                        logger.debug(f"Discarding match {sub_block_name}, {G1.nodes[all_nd[0]]['values']}, {G1.nodes[all_nd[1]]['values']}")
    
                    else:
                        map_list.append(Gsub)
                        logger.debug(f"Matched Lib: {' '.join(Gsub.values())}")
                        logger.debug(f"Matched Circuit: {' '.join(Gsub)}")
                    if len(map_list)>1:
                        fix_order_for_multimatch(G1,map_list,map_list[-1])
    
                mapped_graph_list[sub_block_name] = map_list
    
        return mapped_graph_list
def fix_order_for_multimatch(G1,map_list,Gsub):
    for previous_match in map_list[:-1]:
        if set(Gsub.keys())==set(previous_match.keys()):
            logger.debug(f'fixing repeated node matches {Gsub.keys()} {previous_match.keys()}')
            #delta is an assumed number to define order
            gsub_identifier= '_'.join([Gsub[key] for key in sorted(Gsub.keys())])
            prev_identifier= '_'.join([previous_match[key] for key in sorted(Gsub.keys())])
            if gsub_identifier>prev_identifier:
                logger.debug(f'replacing match, {prev_identifier} with {gsub_identifier}')
                map_list.remove(previous_match)
                return
            else:
                logger.debug('removing new match')
                map_list.remove(Gsub)

#%%

#%%
def dont_touch_clk(Gsub,CLOCK):
    if CLOCK and CLOCK is not None:
        for clk in CLOCK:
            if clk in Gsub:
                return True
    return False
def read_setup(setup_path):
    design_setup = {
            "POWER":['vdd'],
            "GND":[],
            "CLOCK":[],
            "DIGITAL":[],
            "DONT_USE_CELLS":[],
            "NO_CONST":[]
            }
    if os.path.isfile(setup_path):
        logger.debug(f'Reading setup file: {setup_path}')
        fp = open(setup_path, "r")
        line = fp.readline()
        while line:
            if line.strip().startswith("POWER"):
                power = line.strip().split('=')[1].split()
                design_setup['POWER']=power
            elif line.strip().startswith("GND"):
                GND = line.strip().split('=')[1].split()
                design_setup['GND']=GND
            elif line.strip().startswith("CLOCK"):
                CLOCK = line.strip().split('=')[1].split()
                design_setup['CLOCK']=CLOCK
            elif line.strip().startswith("DIGITAL"):
                DIGITAL = line.strip().split('=')[1].split()
                design_setup['DIGITAL']=DIGITAL
            elif line.strip().startswith("DONT_USE_CELLS"):
                DONT_USE_CELLS = line.strip().split('=')[1].split()
                design_setup['DONT_USE_CELLS']=DONT_USE_CELLS
            elif line.strip().startswith("NO_CONST"):
                NO_CONST = line.strip().split('=')[1].split()
                design_setup['NO_CONST']=NO_CONST
            else:
                logger.warning(f"Non identified values found in setup file{line}")
            line=fp.readline()
        logger.debug(f"SETUP: {design_setup}")
    else:
        logger.warning(f"no setup file found: {setup_path}")
    return design_setup

def get_key(Gsub, value):
    return list(Gsub.keys())[list(Gsub.values()).index(value)]




def compare_balanced_tree(G, node1:str, node2:str, traversed1:list, traversed2:list):
    """
    used to remove some false matches for DP and CMC
    """
    logger.debug(f"checking symmtrical connections for nodes: {node1}, {node2}")
    tree1 = set(get_next_level(G,[node1]))
    tree2 = set(get_next_level(G,[node2]))
    #logger.debug("tree1 %s tree2 %s",set(tree1),set(tree2))
    traversed1.append(node1)
    traversed2.append(node2)
    if tree1==tree2:
        #logger.debug("common net or device")
        return True
    while(len(list(tree1))== len(list(tree2)) > 0):
        logger.debug(f"tree1 {tree1} tree2 {tree2} traversed1 {traversed1} traversed2 {traversed2}")
        tree1 = set(tree1) - set(traversed1)
        tree2 = set(tree2) - set(traversed2)
        #logger.debug(f"removed traversed elements tree1 {tree1} tree2 {tree2}")
        #type1 = [G.nodes[node]["inst_type"] for node in list(tree1)]
        #type2 = [G.nodes[node]["inst_type"] for node in list(tree2)]
        if tree1.intersection(tree2) or len(list(tree1))== len(list(tree2))==0:
            #logger.debug("matched subgraph")
            return True
        else:
            traversed1+=list(tree1)
            traversed2+=list(tree2)
            tree1=set(get_next_level(G,tree1))
            tree2=set(get_next_level(G,tree2))
            #logger.debug(f"checking next level:tree1 {tree1} tree2: {tree2}")

    logger.debug(f"Non symmetrical branches for nets: {node1}, {node2}")
    return False
def copy_matched_subcircuit_attributes(G1,G2, Gsub,g2_ports,num,pg):
    # Define ports for subblock
    matched_ports = {}
    ports_weight = {}
    for g1_n, g2_n in Gsub.items():
        if 'mos' in G1.nodes[g1_n]["inst_type"]:
            G2.nodes[g2_n]['values'] = G1.nodes[g1_n]['values']
            G2.nodes[g2_n]['real_inst_type'] = G1.nodes[g1_n]['real_inst_type']

        elif 'net' in G2.nodes[g2_n]["inst_type"]:
            if 'external' in G2.nodes[g2_n]["net_type"]:
                if num > 1 and g1_n in pg:
                    # remove power connections
                    G2=nx.relabel_nodes(G2,{g2_n:g1_n},copy=False)
                else:
                    matched_ports[g2_n] = g1_n
                    ports_weight[g2_n] = []
                    for nbr in list(G2.neighbors(g2_n)):
                        ports_weight[g2_n].append(G2.get_edge_data(g2_n, nbr)['weight'])
        else:
            G2.nodes[g2_n]['values'] = G1.nodes[g1_n]['values']
            G2.nodes[g2_n]['real_inst_type'] = G1.nodes[g1_n]['real_inst_type']
    logger.debug(f"match: {' '.join(Gsub)}")
    logger.debug(f"Matched ports: {' '.join(matched_ports)}")
    logger.debug(f"Matched nets : {' '.join(matched_ports.values())}")
    return matched_ports,ports_weight
def already_merged(G1,Gsub):
    am = False
    for g1_node in Gsub:
        if g1_node not in G1:
            am = True
            logger.debug(f"Skip merging. Node absent: {g1_node}")
            break
    return am


def multiple_instances(G1,new_node,sub_block_name,check_duplicates):
    val_n_type=G1.nodes[new_node]["values"].copy()
    val_n_type["real_inst_type"]=G1.nodes[new_node]["real_inst_type"]
    val_n_type["ports"]=G1.nodes[new_node]["ports"]
    update_name = sub_block_name
    if sub_block_name not in check_duplicates.keys():
        logger.debug(f"adding sub_ckt: {update_name} {val_n_type} {check_duplicates} ")
        check_duplicates[sub_block_name]=[val_n_type]

    elif val_n_type in check_duplicates[sub_block_name]:
        inst_copy = '<'+ str(check_duplicates[sub_block_name].index(val_n_type))+'>'
        if inst_copy != '<0>':
            update_name = sub_block_name + inst_copy
            G1.nodes[new_node]["inst_type"] = sub_block_name
            G1.nodes[new_node]["inst_copy"] = inst_copy
            logger.debug(f"adding modified sub_ckt: {update_name} {check_duplicates.keys()}")
    else:
        inst_copy = '<'+ str(len(check_duplicates[sub_block_name])) + '>'
        update_name = sub_block_name + inst_copy
        G1.nodes[new_node]["inst_type"] = sub_block_name
        G1.nodes[new_node]["inst_copy"] = inst_copy
        logger.debug(f"different size inst {check_duplicates[sub_block_name]} {val_n_type} {inst_copy}")

        check_duplicates[sub_block_name]+=[val_n_type]
    logger.debug(f"list all copies {sub_block_name} {check_duplicates[sub_block_name]}")
    return update_name

def check_nodes(graph_list):
    for local_subckt in graph_list:
        for node, attr in local_subckt["graph"].nodes(data=True):
            if  not attr["inst_type"] == "net":
                for param,value in attr["values"].items():
                    if param == 'model': continue
                    assert (isinstance(value, int) or isinstance(value, float)), \
                        "ERROR: Parameter value %r not defined" %(str(value)+' of '+ node)
