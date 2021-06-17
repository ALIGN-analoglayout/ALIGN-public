# -*- coding: utf-8 -*-
"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""
#%%
import networkx as nx
from networkx.algorithms import isomorphism

from .merge_nodes import merge_nodes, merged_value,convert_unit
from .util import get_next_level
from .find_constraint import FindSymmetry
from .common_centroid_cap_constraint import merge_caps
import pprint
import logging
from ..schema import constraint
from ..schema.hacks import HierDictNode

logger = logging.getLogger(__name__)


#%%

class Annotate:
    """
    Creates hierarchies in the graph based on a library or user defined groupblock constraint
    Boundries (clk,digital, etc) are defined from setup file
    """
    def __init__(self,hier_graph_dict,design_setup,library,existing_generator):
        """
        Args:
            hier_graph_dict (dict): all subckt graph, names and port
            design_setup (dict): information from setup file
            library (list): list of library elements in dict format
            existing_generator (list): list of names of existing generators
        """
        self.hier_graph_dict = hier_graph_dict
        self.digital = design_setup['DIGITAL']
        self.pg = design_setup['POWER']+design_setup['GND']
        self.lib = library
        self.clk = design_setup['CLOCK']
        self.all_lef = existing_generator
        self.stop_points = self.pg+self.clk
        self.no_array = design_setup['NO_ARRAY']+design_setup['DIGITAL']

    def annotate(self):
        """
        main function to creates hierarchies in the block
        iterativily goes through all subckts in the netlist
        Reduce graph to a list of nodes
        Returns:
            list: all updated circuit list
        """
        logger.debug(f"found ckt:{self.hier_graph_dict}")

        names = list(self.hier_graph_dict)

        for name in names:
            circuit_name= name
            G1 = self.hier_graph_dict[name]["graph"]
            self._group_block_const(G1,circuit_name)
            self._group_cap_const(G1,circuit_name)

        for circuit_name in list(self.hier_graph_dict.keys()):
            logger.debug(f"START MATCHING in circuit: {circuit_name}")
            circuit = self.hier_graph_dict[circuit_name]
            G1 = circuit["graph"]
            # map and reduce graph to dictionary
            mapped_graph_list = self._mapped_graph_list(G1, circuit_name, self.pg )
            const_list = self.hier_graph_dict[circuit_name]['constraints']
            self.hier_graph_dict[circuit_name]["graph"] = self._reduce_graph(G1, circuit_name, mapped_graph_list, const_list)
            #Removing single instances of instances. TODO from sy: Generate might be a single instance constraint. The logic below will fail.
            self.hier_graph_dict[circuit_name] = self.hier_graph_dict[circuit_name].copy(
                update={"constraints" : [
                    const
                    for const in const_list
                    if (hasattr(const,'instances') and len(const.instances)>1)
                        or not hasattr(const,'instances')]})
            check_nodes(self.hier_graph_dict)
            logger.debug(f"Grest ckt is {circuit['graph'].nodes(data=True)}")
            if circuit_name not in self.no_array:
                symmetry_blocks = FindSymmetry(circuit["graph"], circuit["ports"], circuit["ports_weight"], self.stop_points)
                for symm_blocks in symmetry_blocks.values():
                    logger.debug(f"generated constraints: {pprint.pformat(symm_blocks, indent=4)}")
                    if isinstance(symm_blocks, dict) and "graph" in symm_blocks.keys():
                        logger.debug(f"added new hierarchy: {symm_blocks['name']} {symm_blocks['graph'].nodes()}")
                        self.hier_graph_dict[symm_blocks['name']] = symm_blocks
                        assert False, "Don't understand what's being deleted here"
                        del self.hier_graph_dict[symm_blocks['name']]['name']

            self.lib_names = [lib_ele['name'] for lib_ele in self.lib]
            for ckt_name, circuit in self.hier_graph_dict.items():
                if 'id' in self.hier_graph_dict[ckt_name] and len(self.hier_graph_dict[ckt_name]['id']) > 1:
                    copies = len(self.hier_graph_dict[ckt_name]['id'])
                    self.lib_names += [ckt_name + '_type' + str(n) for n in range(copies)]
        return self.lib_names

    def _update_attributes(self,circuit_graph,name,lib_name,lib_graph, Gsub):
        """
        Creates a copy of the library element
        Copies attributes from the netlist graph to copied library graph
        Args:
            circuit_graph (graph): graph of netlist subckt
            name (str): name of subckt
            lib_name (str): name of matched library
            lib_graph (graph): graph of library
            Gsub (dict): matching between elements

        Returns:
            matched_ports (dict): matching of library ports to nets in subckt
            ports_weight (dict): weigth of conneted nets
            G2(graph): graph with updated values/attributes
        """
        #PnR can route primitive power but not subckt power
        if lib_name in self.all_lef:
            pg = []
        else:
            pg = self.pg
        G1 = circuit_graph
        num = len([key for key in Gsub
                        if 'net' not in G1.nodes[key]["inst_type"]])
        # Define ports for subblock
        matched_ports = {}
        ports_weight = {}
        G2 = lib_graph.copy()
        for g1_n, g2_n in Gsub.items():
            if 'net' in G2.nodes[g2_n]["inst_type"]:
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
        return matched_ports,ports_weight,G2

    def _group_block_const(self,G1,name):
        if self._if_const(name):
            gb_const = [const for const in self.hier_graph_dict[name]["constraints"] if isinstance(const, constraint.GroupBlocks)]
            const_list = [const for const in self.hier_graph_dict[name]["constraints"] if not isinstance(const, constraint.GroupBlocks)]
            for const in gb_const:
                if not set(const.instances).issubset(set(G1.nodes)):
                    logger.error(f"Constraint instances: {const.instances} not in subcircuit {list(G1.nodes)}")
                    exit()
                logger.debug(f"Grouping instances {const.instances}")
                inst_name = '_'.join(const.instances)
                matched_ports = {}
                ports_weight = {}
                mapping = {}
                for block in const.instances:
                    mapping[block] = block
                    for nbr in G1.neighbors(block):
                        if set(G1.neighbors(nbr)).issubset(set(const.instances)) and \
                            nbr not in self.hier_graph_dict[name]['ports']:
                            continue
                        else:
                            matched_ports[nbr]=nbr
                            if not nbr in ports_weight:
                                ports_weight[nbr] = []
                                ports_weight[nbr].append(G1.get_edge_data(block, nbr)['weight'])
                subgraph,_ = merge_nodes(G1,const.name,const.instances,matched_ports,inst_name)
                sconst = self._top_to_bottom_translation(name, G1, mapping, inst_name, const.name, const_list)
                self.hier_graph_dict[const.name] = HierDictNode(
                    name = const.name,
                    graph = subgraph,
                    ports = list(matched_ports.keys()),
                    ports_weight = ports_weight,
                    constraints = sconst
                    )
                self._update_sym_const(name, G1, [const.name, *const.instances], inst_name, const_list)
                self._update_block_const(name, G1, [const.name, *const.instances], inst_name, const_list)
            #Removing single instances of instances. TODO from sy: Generate might be a single instance constraint. The logic below will fail.
            self.hier_graph_dict[name] = self.hier_graph_dict[name].copy(
                update={"constraints" : [
                    const
                    for const in const_list
                    if (hasattr(const,'instances') and len(const.instances)>1)
                        or not hasattr(const,'instances')]})


    def _group_cap_const(self, G1, name):
        """
        Reads common centroid const in input constraints
        Merges cc caps as single cap in const-file and netlist
        Parameters
        ----------
        graph : networkx graph
            Input graph to be modified
        const_path: pathlib.path
            Input const file path
        ports : list
            Used to check nets which should not be deleted/renamed.
        Returns
        -------
        None.

        """
        if self._if_const(name):
            const_list = self.hier_graph_dict[name]["constraints"]
            logger.debug(f"checking existing GroupCaps constraint {const_list} {G1.nodes}")
            for const in const_list:
                # Check1: atleast one block in defined constraint
                # Check2:  Check block in design
                if isinstance(const, constraint.GroupCaps) \
                    and hasattr(const, 'instances') and len(const.instances) > 1 \
                    and set(const.instances).issubset(set(G1.nodes)):
                    logger.debug(f"Grouping CC caps {const}")
                    ctype = 'Cap_cc_' + "_".join([str(x) for x in const.num_units])
                    merge_caps(G1,ctype,const.instances,const.name)


    def _update_sym_const(self,name,G1,remove_nodes,new_inst, const_list):
        """
        Update instance names in the constraint in case they are reduced

        Args:
            name (str): name of subckt
            G1 (graph): subckt graph
            remove_nodes (list): nodes which are being removed
        """
        logger.debug(f"updating symmetry block constraints of subcircuit {name}, nodes: {remove_nodes}, new name: {new_inst}")
        if self._if_const(name):
            for const in const_list:
                if hasattr(const, 'pairs'):
                    for pair in const.pairs:
                        if len(pair) == 2:
                            if pair[0] in remove_nodes and pair[1] in remove_nodes:
                                pair[0] = new_inst
                                pair.pop()
                                logger.debug(f"updated symmetric pair constraint to self symmetry:{const}")
                            elif pair[0] in remove_nodes and pair[1] not in remove_nodes:
                                pair[0] = new_inst
                            elif pair[1] in remove_nodes and pair[0] not in remove_nodes:
                                pair[1] = new_inst
                        elif len(pair) == 1:
                            if pair[0] in remove_nodes:
                                pair[0] = new_inst
                                logger.debug(f"updated symmetric pair constraint to self symmetry:{const}")


    def _top_to_bottom_translation(self, name, G1, Gsub, new_inst, sub_hierarchy_name, const_list):
        """
        Update instance names in the constraint in case they are reduced

        Args:
            name (str): name of subckt
            G1 (graph): subckt graph
            Gsub (dict): node mapping
        """

        logger.debug(f"transfering constraints from top {name} to bottom {sub_hierarchy_name} ")

        if self._if_const(name):
            if sub_hierarchy_name in self.hier_graph_dict and 'constraints' in self.hier_graph_dict[sub_hierarchy_name]:
                sub_const = self.hier_graph_dict[sub_hierarchy_name]['constraints']
            else:
                sub_const = []
                for const in const_list:
                    if any(isinstance(const, x) for x in [constraint.HorizontalDistance,constraint.VerticalDistance,constraint.BlockDistance]):
                        sub_const.append(const)
                        logger.debug(f"transferring global const {const}")
                    elif hasattr(const, "instances"):
                        logger.debug(f"checking if sub hierarchy instances are in const defined {Gsub} {new_inst} {const} ")
                        sconst = {x:
                            [Gsub[block] for block in const.instances if block in Gsub.keys()]
                            if x == 'instances'
                            else getattr(const, x)
                            for x in const.__fields_set__}
                        assert 'constraint' in sconst
                        logger.debug(f"transferred constraint instances {Gsub} from {const} to {sconst}")
                        if len(sconst['instances']) > 1:
                            sub_const.append(sconst)
        else:
            sub_const = []
        return sub_const


    def _update_block_const(self,name,G1,remove_nodes,new_inst, const_list):
        """
        Update instance names in the constraint in case they are reduced

        Args:
            name (str): name of subckt
            G1 (graph): subckt graph
            remove_nodes (list): nodes which are being removed
        """

        def _list_replace(lst, old_value, new_value):
            for i, value in enumerate(lst):
                if value == old_value:
                    lst[i] = new_value

        logger.debug(f"update constraints with block in them for hierarchy {name} {remove_nodes}")
        if self._if_const(name):
            for const in const_list:
                if hasattr(const, 'instances'):
                    logger.debug(f"checking instances in the constraint:{const.instances} {set(remove_nodes)}")
                    if set(const.instances) & set(remove_nodes):
                        replace = True
                        for block in remove_nodes:
                            if replace:
                                _list_replace(const.instances, block, new_inst)
                                replace = False
                            elif block in const.instances:
                                const.instances.remove(block)
                        logger.debug(f"updated instances in the constraint:{const}")

    def _if_const(self,name):
        return True

    def _reduce_graph(self,circuit_graph,name,mapped_graph_list, const_list):
        """
        merge matched graphs
        """
        logger.debug("START reducing graph: ")
        G1 = circuit_graph.copy()
        for lib_ele in self.lib:
            lib_name = lib_ele['name']
            if lib_name in mapped_graph_list:
                logger.debug(f"Reducing ISOMORPHIC sub_block: {lib_name}{mapped_graph_list[lib_name]}")

                for Gsub in sorted(mapped_graph_list[lib_name], key= lambda i: '_'.join(sorted(i.keys()))):
                    if already_merged(G1,Gsub):
                        continue
                    remove_nodes = [
                        key for key in Gsub
                        if 'net' not in G1.nodes[key]["inst_type"]]
                    logger.debug(f"Reduce nodes: {', '.join(remove_nodes)}")

                    matched_ports,ports_weight,G2 = self._update_attributes(G1,name,lib_name, lib_ele["graph"],Gsub)

                    if len(remove_nodes) == 1:
                        logger.debug(f"One node element: {lib_name}")
                        G1.nodes[remove_nodes[0]]["inst_type"] = lib_name
                        G1.nodes[remove_nodes[0]]["ports_match"] = matched_ports
                        updated_values = merged_value({}, G1.nodes[remove_nodes[0]]["values"])
                        G1.nodes[remove_nodes[0]]["values"] = updated_values
                    else:

                        logger.debug(f"Multi node element: {lib_name} {matched_ports}")
                        subgraph,new_node = merge_nodes(
                            G1, lib_name, remove_nodes, matched_ports)

                        sconst = self._top_to_bottom_translation(name, G1, Gsub, new_node, lib_name, const_list)
                        self._update_sym_const(name, G1, remove_nodes, new_node, const_list)
                        self._update_block_const(name, G1, remove_nodes, new_node, const_list)

                        logger.debug(f"adding new sub_ckt: {lib_name} {sconst}")
                        if lib_name not in self.all_lef:
                            logger.debug(f'Calling recursive for block: {lib_name}')
                            mapped_subgraph_list = self._mapped_graph_list(G2, lib_name)
                            Grest = self._reduce_graph(
                                G2, lib_name,mapped_subgraph_list, sconst)
                        else:
                            Grest = G2
                            for n in remove_nodes:
                                logger.debug(Grest.nodes[Gsub[n]]["values"])
                                for p,v in Grest.nodes[Gsub[n]]["values"].items():
                                    Grest.nodes[Gsub[n]]["values"][p] = convert_unit(v)
                                
                        subckt = HierDictNode(
                            name = 'undefined',
                            graph = Grest,
                            ports = list(matched_ports.keys()),
                            ports_match = matched_ports,
                            ports_weight = ports_weight,
                            constraints = sconst,
                            size = len(subgraph.nodes())
                            )

                        self.multiple_instances(G1,new_node,lib_name,subckt)
                        check_nodes(self.hier_graph_dict)
            logger.debug(f"Finished one branch: {lib_name}")
        return G1

    def _is_small(self,g1,g2):
        nd2 = [g2.nodes[node]["inst_type"] for node in g2.nodes()]
        nd2 = {i:nd2.count(i) for i in nd2}
        nd1 = [g1.nodes[node]["inst_type"] for node in g1.nodes()]
        nd1 = {i:nd1.count(i) for i in nd1}
        is_small = True
        for k,v in nd2.items():
            if k in nd1 and v <= nd1[k]:
                continue
            else:
                is_small=False
        return is_small

    def _is_digital(self,g2,name):
        nd = [node for node in g2.nodes() if 'net' not in g2.nodes[node]["inst_type"]]
        if name in self.digital and len(nd)>1:
            return True
        else:
            return False
    def _is_clk(self,Gsub):
        for clk in self.clk:
            if clk in Gsub:
                return True
        return False

    def _mapped_graph_list(self,G1, name, POWER=None):
        """
        find all matches of library element in the graph
        """
        logger.debug(f"Matching circuit Graph nodes: {G1.nodes} edges:{G1.edges(data=True)}")
        mapped_graph_list = {}
        for lib_ele in self.lib:
            block_name = lib_ele['name']
            if block_name==name:
                continue
            G2 = lib_ele['graph']

            # Digital instances only transistors:
            if self._is_digital(G2,name):
                continue
            if not self._is_small(G1, G2):
                continue

            if len(G2.nodes)<=len(G1.nodes):
                logger.debug(f"Matching: {block_name} : {G2.nodes} {G2.edges(data=True)}")
            GM = isomorphism.GraphMatcher(
                G1, G2,
                node_match = isomorphism.categorical_node_match(['inst_type'],
                                                              ['nmos']),
                edge_match = isomorphism.categorical_edge_match(['weight'], [1]))
            if GM.subgraph_is_isomorphic():
                logger.debug(f"ISOMORPHIC : {block_name}")
                map_list = []

                for Gsub in GM.subgraph_isomorphisms_iter():

                    all_nd = [key for key in Gsub.keys() if 'net' not in G1.nodes[key]["inst_type"]]
                    logger.debug(f"matched inst: {all_nd}")
                    if len(all_nd)>1 and self._is_clk(Gsub):
                        logger.debug("Discarding match due to clock")
                        continue
                    if block_name.startswith('DP')  or block_name.startswith('CMC'):
                        if G1.nodes[all_nd[0]]['values'] == G1.nodes[all_nd[1]]['values'] and \
                            compare_balanced_tree(G1,get_key(Gsub,'DA'),get_key(Gsub,'DB'),[all_nd[0]],[all_nd[1]]) :
                            if 'SA' in Gsub.values() and \
                            compare_balanced_tree(G1,get_key(Gsub,'SA'),get_key(Gsub,'SB'),[all_nd[0]],[all_nd[1]]):
                                map_list.append(Gsub)
                                logger.debug(f"Matched Lib: {' '.join(Gsub.values())}")
                                logger.debug(f"Matched Circuit: {' '.join(Gsub)}")
                            # remove pseudo diff pair
                            elif block_name.startswith('DP') and POWER is not None and get_key(Gsub,'S') in POWER:
                                logger.debug(f"skipping pseudo DP {POWER}: {' '.join(Gsub)}")
                            else:
                                map_list.append(Gsub)
                                logger.debug(f"Matched Lib: {' '.join(Gsub.values())}")
                                logger.debug(f"Matched Circuit: {' '.join(Gsub)} power:{POWER}")
                        else:
                            logger.debug(f"Discarding match {block_name} due to non matching branches")
                    elif block_name.startswith('SCM') and G1.nodes[all_nd[0]]['values'] != G1.nodes[all_nd[1]]['values']:
                        logger.debug(f"Discarding match {block_name} due to value mismatch")

                    else:
                        map_list.append(Gsub)
                        logger.debug(f"Matched Lib: {' '.join(Gsub.values())}")
                        logger.debug(f"Matched Circuit: {' '.join(Gsub)}")
                    if len(map_list)>1:
                        fix_order_for_multimatch(G1,map_list,map_list[-1])
                mapped_graph_list[block_name] = map_list

        return mapped_graph_list

    def multiple_instances(self,G1,new_node,block_name,subckt):
        val_n_type = G1.nodes[new_node]["values"].copy()
        val_n_type["real_inst_type"]=G1.nodes[new_node]["real_inst_type"]
        val_n_type["ports"]=G1.nodes[new_node]["ports"]
        # TODO: We should also examine the constraint list
        update_name = block_name
        if block_name not in self.hier_graph_dict.keys():
            logger.debug(f"adding sub_ckt: {update_name} {val_n_type} ")
            self.hier_graph_dict[block_name]=subckt.copy(update={'name': block_name})
            check_nodes(self.hier_graph_dict)
            self.hier_graph_dict[block_name]['id']=[val_n_type]
        elif val_n_type in self.hier_graph_dict[block_name]['id']:
            inst_copy = '<'+ str(self.hier_graph_dict[block_name]['id'].index(val_n_type))+'>'
            if inst_copy != '<0>':
                update_name = block_name + inst_copy
                G1.nodes[new_node]["inst_type"] = block_name
                G1.nodes[new_node]["inst_copy"] = inst_copy
                logger.debug(f"adding modified sub_ckt: {update_name} {self.hier_graph_dict.keys()}")
                self.hier_graph_dict[update_name]=subckt.copy(update={'name': update_name})
        else:
            inst_copy = '<'+ str(len(self.hier_graph_dict[block_name]['id'])) + '>'
            update_name = block_name + inst_copy
            G1.nodes[new_node]["inst_type"] = block_name
            G1.nodes[new_node]["inst_copy"] = inst_copy
            logger.debug(f"different size inst {self.hier_graph_dict[block_name]['id']} {val_n_type} {inst_copy}")
            self.hier_graph_dict[update_name]=subckt.copy(update={'name': update_name})
            self.hier_graph_dict[block_name]['id']+=[val_n_type]
        logger.debug(f"list all copies {block_name} {self.hier_graph_dict[block_name]['id']}")
#%%
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


def get_key(Gsub, value):
    return list(Gsub.keys())[list(Gsub.values()).index(value)]

def compare_balanced_tree(G, node1:str, node2:str, traversed1:list, traversed2:list):
    """
    used to remove some false matches for DP and CMC
    """
    logger.debug(f"checking symmtrical connections for nodes: {node1}, {node2}")
    tree1 = set(get_next_level(G,[node1]))
    tree2 = set(get_next_level(G,[node2]))
    traversed1.append(node1)
    traversed2.append(node2)
    if tree1==tree2:
        return True
    while(len(list(tree1))== len(list(tree2)) > 0):
        logger.debug(f"tree1 {tree1} tree2 {tree2} traversed1 {traversed1} traversed2 {traversed2}")
        tree1 = set(tree1) - set(traversed1)
        tree2 = set(tree2) - set(traversed2)

        if tree1.intersection(tree2) or len(list(tree1))== len(list(tree2))==0:
            return True
        else:
            traversed1+=list(tree1)
            traversed2+=list(tree2)
            tree1=set(get_next_level(G,tree1))
            tree2=set(get_next_level(G,tree2))

    logger.debug(f"Non symmetrical branches for nets: {node1}, {node2}")
    return False



def already_merged(G1,Gsub):
    am = False
    for g1_node in Gsub:
        if g1_node not in G1:
            am = True
            logger.debug(f"Skip merging. Node absent: {g1_node}")
            break
    return am


def check_nodes(graph_dict):
    for local_subckt in graph_dict.values():
        if not 'ports_match' in local_subckt:
            continue
        for node, attr in local_subckt["graph"].nodes(data=True):
            if  not attr["inst_type"] == "net":
                for param,value in attr["values"].items():
                    if param == 'model': continue
                    assert (isinstance(value, int) or isinstance(value, float)) or value=="unit_size", \
                        "ERROR: Parameter value %r not defined" %(str(value)+' of '+str(type(value))+' of'+ node)
