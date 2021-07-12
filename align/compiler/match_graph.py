# -*- coding: utf-8 -*-
"""
Created on Fri Nov  2 21:33:22 2018

@author: kunal
"""
#%%
from re import sub
from align.schema import model
import networkx as nx
from networkx.algorithms import isomorphism
from align.schema.subcircuit import SubCircuit

from ..schema.types import set_context
from .merge_nodes import merge_nodes, merged_value,convert_unit
from .util import get_next_level
from .find_constraint import FindSymmetry
from .common_centroid_cap_constraint import merge_caps
import pprint
import logging
from ..schema import constraint
from ..schema.instance import Instance
from ..schema.hacks import HierDictNode
from ..schema.types import set_context
from align.schema.graph import Graph
logger = logging.getLogger(__name__)


#%%

class Annotate:
    """
    Creates hierarchies in the graph based on a library or user defined groupblock constraint
    Boundries (clk,digital, etc) are defined from setup file
    """
    def __init__(self,ckt_data,design_setup,library,existing_generator):
        """
        Args:
            ckt_data (dict): all subckt graph, names and port
            design_setup (dict): information from setup file
            library (list): list of library elements in dict format
            existing_generator (list): list of names of existing generators
        """
        self.ckt_data = ckt_data
        self.digital = design_setup['DIGITAL']
        self.pg = design_setup['POWER']+design_setup['GND']
        self.lib = library
        self.clk = design_setup['CLOCK']
        self.all_lef = existing_generator
        self.stop_points = self.pg+self.clk
        self.no_array = design_setup['NO_ARRAY']+design_setup['DIGITAL']
        self.lib_names = [lib_ele.name for lib_ele in library]

    def _is_skip(self,ckt):

        di_const = [const.instances for const in ckt.constraints if isinstance(const, constraint.DoNotIdentify)]
        #Changing 2D list to 1D list
        if len(di_const)>0:
            di_const = [x for y in di_const for x in y]
        return di_const
    def annotate(self):
        """
        main function to creates hierarchies in the block
        iterativily goes through all subckts in the netlist
        Reduce graph to a list of nodes
        Returns:
            list: all updated circuit list
        """
        logger.debug(f"ALl  subckt:{[ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]}")

        # names = list(self.ckt_data)
        for ckt in self.ckt_data:
            if isinstance(ckt, SubCircuit):
                circuit_name= ckt.name
                self._group_block_const(circuit_name)
        logger.debug(f"ALl subckt after grouping:{[ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]}")

                #self._group_cap_const(subckt)
        traversed = [] # libray gets appended, so only traverse subckt once
        temp_match_dict ={} # To avoid iterative calls (search subckt in subckt)
        for ckt in self.ckt_data:
            if isinstance(ckt, SubCircuit) and ckt.name not in self.all_lef and ckt.name not in traversed:
                netlist_graph= Graph(ckt)
                skip_nodes = self._is_skip(ckt)
                logger.debug(f"START MATCHING in circuit: {ckt.name} count: {len(ckt.elements)} ele: {ckt.elements} traversed: {traversed} skip: {skip_nodes}")
                traversed.append(ckt.name)
                for subckt in self.lib:
                    if subckt.name == ckt.name or (subckt.name in temp_match_dict and ckt.name in temp_match_dict[subckt.name]):
                        continue
                    new_subckts = netlist_graph.replace_matching_subgraph(Graph(subckt),skip_nodes)
                    if subckt.name in temp_match_dict:
                        temp_match_dict[subckt.name].extend(new_subckts)
                    else:
                        temp_match_dict[subckt.name] = new_subckts
                    if len(new_subckts) >=1:
                        logger.debug(f"Matching subckt {subckt.name}: {len(new_subckts)}")
                # circuit = self.ckt_data[circuit_name]
                # G1 = circuit["graph"]
                # map and reduce graph to dictionary
                # mapped_graph_list = self._mapped_graph_list(G1, circuit_name, self.pg )
                # const_list = self.ckt_data[circuit_name]['constraints']
                # self.ckt_data[circuit_name]["graph"] = self._reduce_graph(G1, circuit_name, mapped_graph_list, const_list)
                # #Removing single instances of instances
                # self.ckt_data[circuit_name] = self.ckt_data[circuit_name].copy(
                #     update={"constraints" : [
                #         const
                #         for const in const_list
                #         if (hasattr(const,'instances') and len(const.instances)>1)
                #             or not hasattr(const,'instances')]})
                # check_nodes(self.ckt_data)
                # logger.debug(f"Grest ckt is {circuit['graph'].nodes(data=True)}")
                # if circuit_name not in self.no_array:
                #     symmetry_blocks = FindSymmetry(circuit["graph"], circuit["ports"], circuit["ports_weight"], self.stop_points)
                #     for symm_blocks in symmetry_blocks.values():
                #         logger.debug(f"generated constraints: {pprint.pformat(symm_blocks, indent=4)}")
                #         if isinstance(symm_blocks, dict) and "graph" in symm_blocks.keys():
                #             logger.debug(f"added new hierarchy: {symm_blocks['name']} {symm_blocks['graph'].nodes()}")
                #             self.ckt_data[symm_blocks['name']] = symm_blocks
                #             assert False, "Don't understand what's being deleted here"
                #             del self.ckt_data[symm_blocks['name']]['name']


                # for ckt_name, circuit in self.ckt_data.items():
                #     if 'id' in self.ckt_data[ckt_name] and len(self.ckt_data[ckt_name]['id']) > 1:
                #         copies = len(self.ckt_data[ckt_name]['id'])
                #         self.lib_names += [ckt_name + '_type' + str(n) for n in range(copies)]
                logger.debug(f"Circuit after MATCHING: {ckt.name} {ckt.elements}")
        logger.info(f"Subcircuits after creating primitive hiearchy {[ckt.name for ckt in self.ckt_data if isinstance(ckt, SubCircuit)]}")
        return self.lib_names

    def _check_const_length(self,const_list,const):
        is_append = False
        try:
            with set_context(const_list):
                if hasattr(const,'instances') and len(const.instances)>0:
                    is_append = True
                elif isinstance(const,dict) and 'instances' in const and len(const["instances"])>0:
                    is_append = True
                elif isinstance(const,dict) and 'instances' not in const:
                    is_append = True
                elif isinstance(const,dict) and 'instances' in const and len(const["instances"])==0:
                    logger.info(f"skipping const of zero length: {const}")
                elif not hasattr(const,'instances'):
                    is_append = True
                else:
                    logger.debug(f"invalid constraint {const}")
                if is_append == True and const not in const_list:
                    logger.debug(f"constraint appended: {const}")
                    const_list.append(const)
        except:
            logger.debug(f"skipping invalid constraint {const}")


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
        if lib_ele.name in self.all_lef:
            pg = []
        else:
            pg = self.pg
        G1 = circuit_graph
        num = len(lib_ele.elements)
        # Define ports for subblock
        matched_ports = {}
        ports_weight = {}
        G2 = Graph(lib_ele) #TBD: needed a copy here
        lib_ele_copy = lib_ele.copy()
        # print(lib_ele_copy)
        # pins = self.ckt_data.find(lib_ele.name).pins

        for g1_n, g2_n in Gsub.items():
            # if 'instance' not in G2.nodes[g2_n]:
            #     if 'external' in G2.nodes[g2_n]["net_type"]:
            #         if num > 1 and g1_n in pg:
            #             # remove power connections
            #             G2=nx.relabel_nodes(G2,{g2_n:g1_n},copy=False)
            #         else:
            #             matched_ports[g2_n] = g1_n
            #             ports_weight[g2_n] = []
            #             for nbr in list(G2.neighbors(g2_n)):
            #                 ports_weight[g2_n].append(G2.get_edge_data(g2_n, nbr)['weight'])
            # else:
            if g2_n in lib_ele_copy.elements:
                ele=lib_ele.get_element(g2_n)
                with set_context(lib_ele_copy.elements):
                    ele = Instance(
                        name = ele.name,
                        model = ele.model,
                        pins = ele.pins,
                        parameters = G1.nodes[g1_n]["instance"].parameters
                    )
            else:
                matched_ports[g2_n] = g1_n


        return matched_ports,ports_weight,G2

    def _group_block_const(self,name):
        subckt = self.ckt_data.find(name)
        const_list = subckt.constraints

        if not const_list:
            return

        gb_const = [const for const in const_list if isinstance(const, constraint.GroupBlocks)]
        #reduced_const_list = [const for const in const_list if not isinstance(const, constraint.GroupBlocks)]
        with set_context(subckt.constraints):
            start_count = len(subckt.constraints)
            for const in gb_const:
                subckt.constraints.remove(const)
            assert len(subckt.constraints) == start_count - len(gb_const)

        for const in gb_const:
            assert self.ckt_data.find(const.name.upper()) ==None, \
                f"Already existing subckt with this name, please provide different name to const"
            const_inst = [i.upper() for i in const.instances]
            ckt_ele = set([ele.name for ele in subckt.elements])
            assert set(const_inst).issubset(ckt_ele) , f"Constraint instances: {const_inst} not in subcircuit {subckt.name}"
            # ac_nets : all nets connected to group block instances
            ac_nets = [ele.pins.values() for ele in subckt.elements if ele.name in const_inst]
            ac_nets = set([x for y in ac_nets for x in y])
            ac_nets = [net for net in ac_nets \
                if any(net in ele.pins.values() for ele in subckt.elements \
                    if not ele.name in const_inst)] + list(ac_nets & set(subckt.pins))

            logger.debug(f"Grouping instances {const_inst} in subckt {const.name.upper()} pins: {ac_nets}")
            inst_name = 'X'+'_'.join(const_inst)
            with set_context(self.ckt_data):
                new_subckt = SubCircuit(
                    name = const.name.upper(),
                    pins = ac_nets
                )
                self.ckt_data.append(new_subckt)
            with set_context(new_subckt.elements):
                for e in const_inst:
                    new_subckt.elements.append(subckt.get_element(e))
            with set_context(subckt.elements):
                for e in const_inst:
                    subckt.elements.remove(subckt.get_element(e))
                X1 = Instance(name=inst_name, model=const.name.upper(), pins={x:x for x in ac_nets})
                subckt.elements.append(X1)

            # sconst = self._top_to_bottom_translation(name, G1, mapping, inst_name, const.name, const_list)
            # for c in list(sconst):
            #     self._check_const_length(self.hier_graph_dict[const.name].constraints, c)
            self._update_const(name, [const.name.upper(), *const.instances], inst_name)
        #Removing single instances of instances. TODO from sy: DoNotIdentify might have a single instance!
        # for const in list(const_list):
        #     self._check_const_length(self.hier_graph_dict[name].constraints,const)

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
            const_list = self.ckt_data[name]["constraints"]
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
            if sub_hierarchy_name in self.ckt_data and 'constraints' in self.ckt_data[sub_hierarchy_name]:
                sub_const = self.ckt_data[sub_hierarchy_name]['constraints']
            else:
                sub_const = []
                for const in list(const_list):
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
                        sub_const.append(sconst)
        else:
            sub_const = []
        return sub_const


    def _update_const(self,name,remove_nodes,new_inst):
        """
        Update instance names in the constraint in case they are reduced by groupblock

        Args:
            name (str): name of subckt
            G1 (graph): subckt graph
            remove_nodes (list): nodes which are being removed
        """

        def _list_replace(lst, old_value, new_value):
            for i, value in enumerate(lst):
                if value == old_value:
                    lst[i] = new_value

        logger.debug(f"update constraints with blocks:{remove_nodes} for hierarchy {name} ")
        const_list = self.ckt_data.find(name).constraints
        for const in const_list:
            if hasattr(const, 'instances'):
                logger.debug(f"checking instances in the constraint:{const.instances} {set(remove_nodes)}")
                if set(const.instances) & set(remove_nodes):
                    replace = True
                    for old_inst in remove_nodes:
                        if replace:
                            _list_replace(const.instances, old_inst, new_inst)
                            replace = False
                        elif old_inst in const.instances:
                            const.instances.remove(old_inst)
                    logger.debug(f"updated instances in the constraint:{const}")
            elif hasattr(const, 'pairs'):
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
                            logger.debug(f"updated self symmetric constraint block:{const}")

    def _is_digital(self,g2,name):
        nd = [node for node in g2.nodes() if 'instance' in g2.nodes[node]]
        if name in self.digital and len(nd)>1:
            return True
        else:
            return False
    def _is_clk(self,Gsub):
        for clk in self.clk:
            if clk in Gsub:
                return True
        return False

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