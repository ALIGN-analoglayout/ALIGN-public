# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 13:04:45 2018

@author: kunal
"""

import os
import networkx as nx

from .basic_element import _parse_inst

import logging
logger = logging.getLogger(__name__)

class SpiceParser:
    """
    Read a spice file (.sp/.cdl) and converts it to a graph.
    Device properties are inherited from BasicElement.py
    You can flatten the circuit by using flag: flat
    The final graph is stored in a yaml file in circuit_graphs folder.
    """

    def __init__(self, netlistPath, top_ckt_name=None, flat=0):
        self.netlist = netlistPath
        self.subckts = {}
        self.circuits_list = []
        self.params = {}
        self._global = []
        self.option = []
        self.top_insts = []
        self.include = []
        self.top_ckt_name = top_ckt_name
        self.flat = flat
        self.next_line = None
        self.prev_line = None
        self.check_next_line = None
        logger.debug(f'creating an instance of SpiceParser: {self.top_ckt_name} flat={self.flat}')

    def sp_parser(self):
        """Parse the defined file line wise"""

        if not os.path.isfile(self.netlist):
            logger.error(f"File doesn't exist {self.netlist}")
        else:
            logger.debug(f"File exist: {self.netlist}")
            fp_l = open(self.netlist, "r")
            line = self.get_next_line(fp_l, 1)
            while ".END" not in line:
                # if "**" in line.lower(): pass
                if any(c in line.lower() for c in ("//", "**",'*.')):
                    #line = fp_l.readline()
                    pass
                elif not line.strip():
                    pass
                elif "global" in line.lower():
                    self._parse_global(line, fp_l)
                elif ".temp" in line.lower():
                    temp_line = line
                    logger.debug(f"Temp line: {temp_line}")
                elif ".option" in line.lower():
                    self._parse_option(line, fp_l)
                elif "subckt" in line.lower() and not "subckts" in line.lower():
                    self._parse_subckt_info(line, fp_l)
                elif "include" in line.lower() or "info" in line.lower():
                    self._parse_include(line, fp_l)
                elif "param" in line.lower():
                    check_param = self._parse_param(line, fp_l)
                    if check_param:
                        if self.params:
                            self.params.update(check_param)
                        else:
                            self.params = check_param
                else:
                    parsed_inst = _parse_inst(line)
                    if parsed_inst:
                        self.top_insts.append(parsed_inst)
                line = self.get_next_line(fp_l, 1)
                if not line:
                    break
            logger.debug("PARSING INPUT NETLIST FILE DONE")
            if self.params:
                for param, value in self.params.items():
                    logger.debug(f'Found top_param: {param}, value:{value}')
            elif self.option:
                self.option = filter(lambda a: a != '+', self.option)
            elif self._global:
                self._global = filter(lambda a: a != '+', self._global)
            logger.debug(f"List of subckts in design: {' '.join(self.subckts)}")

# %%
            ## remove source from testbench circuit
            self._remove_source()

            if not self.top_ckt_name :
                logger.debug("No top circuit name provided, returning multiple graphs")
                for name in self.subckts:
                    design = self._hier_circuit(name)
                    subckt_graph = self._create_bipartite_circuit_graph(
                        design, self.subckts[name]["ports"])
                    self.circuits_list.append({
                        "name": name,
                        "graph": subckt_graph,
                        "ports": self.subckts[name]["ports"],
                    })
            elif self.top_insts and self.top_ckt_name not in self.subckts.keys():
                logger.debug(
                    f'Instances found at top, adding dummy subckt: {self.top_ckt_name}')
                if self.params:
                    self.resolve_top_param()

                self.subckts[self.top_ckt_name] = {
                     "ports": [],
                    "nodes": self.top_insts,
                    "params": self.params
                }
                design=self.resolve_hierarchy()
                circuit_graph = self._create_bipartite_circuit_graph(
                    design, [])
                for node, attr in circuit_graph.nodes(data=True):
                    if 'net' in attr['inst_type'] and \
                    len(list(circuit_graph.neighbors(node)))==1:
                        circuit_graph.nodes[node]["net_type"]="external"
                        self.subckts[self.top_ckt_name]["ports"].append(node)
                self.circuits_list.append({
                    "name": self.top_ckt_name,
                    "graph": circuit_graph,
                    "ports": self.subckts[self.top_ckt_name]["ports"],
                })

            elif self.top_ckt_name in self.subckts.keys():
                design=self.resolve_hierarchy()
                subckt_ports = self.subckts[self.top_ckt_name]["ports"]
                circuit_graph = self._create_bipartite_circuit_graph(design, subckt_ports)
                self.circuits_list.append({
                    "name": self.top_ckt_name,
                    "graph": circuit_graph,
                    "ports": self.subckts[self.top_ckt_name]["ports"],
                })
            else:
                logger.error("No design found")
                return 0

            logger.debug(
                "################### PARSING DONE #################### \n")

            logger.debug(
                "\n###################\
                FINAL CIRCUIT AFTER initialization #################### \n"
            )
            for node in design:
                logger.debug(node)

            return self.circuits_list
    def resolve_hierarchy(self):
        if self.flat:
            logger.debug(f"Flatten circuit: {self.top_ckt_name}")
            design = self._flatten_circuit(self.top_ckt_name)
        else:
            design = self._hier_circuit(self.top_ckt_name)
        return design

    def resolve_top_param(self):
        for index, node in enumerate(self.top_insts):
            if "values" in node.keys():
                for param, value in node["values"].items():
                    if '*' in value:
                        logger.debug ("found function in values")
                        value_function = value.split('*')
                        for val in value_function:
                            try:
                                mult=int(val)
                            except:
                                value=val
                    if value in self.params:
                        self.top_insts[index]["values"][param] = self.params[value]
                        try:
                            mult
                        except NameError:
                            self.top_insts[index]["values"][param] = self.top_insts[index]["values"][param]
                        else:
                            self.top_insts[index]["values"][param] =  str(mult)+'*'+self.top_insts[index]["values"][param]
                            del mult
                        logger.debug(
                            f'assigning top parameter {param} value {self.top_insts[index]["values"][param]} to node: {node["inst"]}')
            else:
                logger.error(f'No sizing info:{node["inst"]}')
    def _remove_source(self):
        no_of_source = 0
        for ckt_name, elements in self.subckts.items():
            reduced_subckt = []
            source_ports =[]
            for node in elements["nodes"]:
                if 'source' in node["inst_type"]:
                    source_ports +=node["ports"]
                else:
                    reduced_subckt.append(node)

            no_of_source += len(
                self.subckts[ckt_name]["nodes"]) - len(reduced_subckt)
            self.subckts[ckt_name]["nodes"] = reduced_subckt
            self.subckts[ckt_name]["ports"] += source_ports
        if no_of_source >0:
            logger.warning(f'REMOVED {no_of_source} sources from circuit.')

    def get_next_line(self, file_pointer, line_type):
        if line_type == 1:
            self.prev_line = self.next_line
            if self.check_next_line:
                self.next_line = self.check_next_line
            else:
                self.check_next_line = file_pointer.readline()
                self.next_line = self.check_next_line

            self.check_next_line = file_pointer.readline()
            while self.next_line.strip().endswith('\\') or \
                self.check_next_line.strip().startswith('+') \
                or (self.check_next_line and not self.check_next_line.strip()):
                self.next_line = self.next_line.strip() + self.check_next_line
                self.check_next_line = file_pointer.readline().strip()
            self.next_line = self.next_line.replace('+', '')
            self.next_line = self.next_line.replace('\\','')
        elif line_type == -1:
            self.next_line = self.prev_line
        elif line_type == 0:
            self.next_line = self.next_line
        return self.next_line

    def _parse_subckt_info(self, line, fp_l):
        """ Read subckt line """
        logger.debug(f'started reading subckt: {line.strip()}')
        subckt_nodes = line.strip().split()
        subckt_name = subckt_nodes[1]

        #added to avoid assertion for string in PnR
        if subckt_name[0].isdigit():
            subckt_name = "align_"+subckt_name
        line = self.get_next_line(fp_l, 1)
        nodes, params = self._parse_subckt(line, fp_l)

        self.subckts[subckt_name] = {
            "ports": subckt_nodes[2:],
            "nodes": nodes,
            "params": params
        }
        logger.debug(f'Finished reading subckt: {subckt_name}')

    def _parse_subckt(self, line, fp_l):
        """ Read all lines in subckt"""
        insts = []
        subckt_param_all = {}
        while not (line.lower().startswith('end')
                   or line.lower().startswith('.end')):
            if any(c in line.lower() for c in ("//", '*')):
                line = self.get_next_line(fp_l, 1)
                pass
            elif 'param' in line.lower():
                subckt_param = self._parse_param(line, fp_l)
                if subckt_param:
                    if subckt_param_all:
                        subckt_param_all.update(subckt_param)
                    else:
                        subckt_param_all = subckt_param
                    for param,value in subckt_param.items():
                        logger.debug('Found subckt param: %s, value:%s', param, value);
                line = self.get_next_line(fp_l, 1)
            else:
                node1 = _parse_inst(line)
                if node1:
                    insts.append(node1)
                line = self.get_next_line(fp_l, 1)

        return insts, subckt_param_all

    def _parse_param(self, line, fp_l):
        """Reads and store all parameters"""
        param_list = {}
        logger.debug(f"param: {line}")
        all_param = line.lower().strip().split()
        for idx, individual_param in enumerate(all_param):
            if '=' in individual_param:
                [param, value] = individual_param.split('=')
                if not param:
                    param = all_param[idx - 1]
                if not value:
                    value = all_param[idx + 1]
                logger.debug(f'Found parameters: {param}, value: {value}')
                param_list[param] = value
        return param_list

    def _parse_global(self, line, fp_l):
        """ Read all global lines"""
        logger.debug(f"global: {line}")
        self._global = line.strip().split()

    def _parse_include(self, line, fp_l):
        logger.debug(f"include: {line}")
        self.include.append(line.strip())

    def _parse_option(self, line, fp_l):
        logger.debug(f"option: {line}")
        self.option = line.strip().split()

    def _resolve_param(self, inherited_param, node, values):
        logger.debug(f"node {node} inherited parameter: {inherited_param}" )
        if "values" in node.keys():
            for param, value in node["values"].items():
                logger.debug(f"checking parameter: {param} = {value}")
                if '*' in value:
                    logger.debug ("found function in values")
                    value_function = value.split('*')
                    for val in value_function:
                        try:
                            mult=int(val)
                        except ValueError:
                            value=val

                if value in inherited_param.keys():
                    values[param] = inherited_param[value]
                    try:
                        mult
                    except NameError:
                        values[param] =values[param]
                    else:
                        values[param] *=  mult
                    logger.debug(
                        f'assigning inherited parameter:{param}, {inherited_param[value]} to device: {node["inst"]}')
                else:
                    values[param] = value

    def _flatten_circuit(self,
                         subckt_name,
                         subckt_inst="",
                         connected_nets="",
                         inherited_param={}):
        """
        Transform netlist to a flat graph

        Parameters
        ----------
        subckt_name : TYPE. string
            DESCRIPTION. name of subckt. First call should be from top level
        connected_nets : TYPE, list of nets connected to ports
            DESCRIPTION. The default is "".
        inherited_param : TYPE, parameters passed to subckt
            DESCRIPTION. The default is None.

        Returns
        -------
        flat_design : TYPE, networkx graph
            DESCRIPTION. flat graph of netlist

        """
        flatdesign = []
        ## FIX for UT Austin circuit
        if not inherited_param:
            inherited_param = {**self.params, **self.subckts[subckt_name]["params"]}
        else:
            inherited_param = {**self.params, **inherited_param}
            inherited_param = { **self.subckts[subckt_name]["params"],**inherited_param}
            #inherited_param = {**inherited_param, **self.subckts[subckt_name]["params"]}

        logger.debug(f"flattening the circuits below: {subckt_name}, {subckt_inst}, {connected_nets}, {inherited_param}")
        ### node is not local copy and modifying it modifies dictionary
        for node in self.subckts[subckt_name]["nodes"]:
            logger.debug(f"checking nets of node: {node['inst']} ports:{' '.join(node['ports'])}")
            modified_ports = []
            for net_name in node["ports"]:
                if net_name not in self.subckts[subckt_name]["ports"]:
                    net_name = subckt_inst + net_name
                    logger.debug(f"Net internal to subckt {subckt_name}: {net_name}")
                elif connected_nets:
                    net_name = connected_nets[self.subckts[subckt_name]
                                              ["ports"].index(net_name)]
                    logger.debug(f"Net is part of higher level subckt: {net_name}")
                else:
                    logger.debug(
                        f'net lies in top level net in: {node["inst"]} net_name: {net_name}')
                modified_ports.append(net_name)
            values = node["values"].copy()
            if inherited_param:
                self._resolve_param(inherited_param, node, values)


            if node["inst_type"] in self.subckts:
                flatdesign.extend(
                    self._flatten_circuit(node["inst_type"],
                                          subckt_inst + node["inst"] + '|',
                                          list(modified_ports), values))
            else:
                flat_node = {
                    "inst": subckt_inst + node["inst"],
                    "inst_type": node["inst_type"],
                    "real_inst_type": node["real_inst_type"],
                    "ports": modified_ports,
                    "values": values,
                    "edge_weight": node["edge_weight"]
                }
                logger.debug(f'{flat_node}')
                flatdesign.append(flat_node)
                logger.debug(f'Updated Node name: {flat_node["inst"]}, type: {flat_node["inst_type"]}')

        logger.debug(f"Total no of nodes in design {subckt_name} = {len(flatdesign)}")
        return flatdesign

    def _hier_circuit(self,
                      subckt_name,
                      connected_nets="",
                      inherited_param=None):
        """
        Transform netlist to a hierarchical dictionary

        Parameters
        ----------
        subckt_name : TYPE. string
            DESCRIPTION. name of subckt. First call should be from top level
        connected_nets : TYPE, list of nets connected to ports
            DESCRIPTION. The default is "".
        inherited_param : TYPE, parameters passed to subckt
            DESCRIPTION. The default is None.

        Returns
        -------
        hier_design : TYPE, list
            DESCRIPTION. hierarchical list of netlist

        """
        logger.debug (f"subcktparameters: {inherited_param}")
        hier_design = []
        ## FIX for UT Austin circuit
        if not inherited_param:
            inherited_param = {**self.params, **self.subckts[subckt_name]["params"]}
        else:
            inherited_param = {**self.params, **inherited_param}
            inherited_param = { **self.subckts[subckt_name]["params"],**inherited_param}

        logger.debug(f"making hierarchical circuits: {subckt_name} params: {inherited_param}")
        for node in self.subckts[subckt_name]["nodes"]:
            logger.debug(f"node info: {node}")
            values = node["values"].copy()
            if inherited_param:
                self._resolve_param(inherited_param, node, values)
                logger.debug(f"updated circuit params are: {inherited_param}")
            if node["inst_type"] in self.subckts:
                logger.debug(f'FOUND hier_node: {node["inst_type"]}')

                hier_node = {
                    "inst": node["inst"],
                    "inst_type": node["inst_type"],
                    "real_inst_type": node["real_inst_type"],
                    "ports": node["ports"],
                    "values": values,
                    "hier_nodes": self._hier_circuit(node["inst_type"], self.subckts[subckt_name]["ports"], values)
                }
                hier_design.append(hier_node)
                logger.debug(f"updated node info: {node}")
            else:
                hier_design.append(node)
                hier_design[-1]["values"]=values
        return hier_design

    def _create_bipartite_circuit_graph(self, all_nodes, inout_ports):
        logger.debug(f"Creating bipartitie graph, devices:{len(all_nodes)}")
        circuit_graph = nx.Graph()
        for node in all_nodes:
            if "hier_nodes" in node.keys():
                subgraph = self._create_bipartite_circuit_graph( node["hier_nodes"], self.subckts[node["inst_type"]]["ports"])
                # Define ports for subblock
                connection = {}
                for idx, pin in enumerate(self.subckts[node["inst_type"]]["ports"]):
                        connection[pin] = node['ports'][idx]
                self.subckts[node["inst_type"]]["ports"]
                ports_weight=[]
                for port in self.subckts[node["inst_type"]]["ports"]:
                    port_weight=0
                    if port in subgraph.nodes():
                        #if statement is to skip ports which are only connected to body
                        for nbr in subgraph.neighbors(port):
                            port_weight |= subgraph.get_edge_data(nbr, port)['weight']
                    ports_weight.append(port_weight)
                node['edge_weight']=ports_weight

                # for node in hier_nodes: edge_wt | node["edge_weight"]
                logger.debug(f"Creating sub-graph for node: {node}")
            else:
                subgraph = None
                connection = None
            logger.debug(f"Reading node: {node}")
            circuit_graph.add_node(node["inst"],
                                   inst_type=node["inst_type"],
                                   real_inst_type=node["real_inst_type"],
                                   ports=node['ports'],
                                   edge_weight=node['edge_weight'],
                                   values=node['values'],
                                   sub_graph=subgraph,
                                   connection=connection)
            ##### ASSIGNING EDGE WEIGHTS ######
            #wt_index = 0
            for wt_index, net in enumerate(node["ports"]):
                if "edge_weight" in node.keys():
                    edge_wt = node["edge_weight"][wt_index]
                    logger.debug(f"Using existing weights {edge_wt} for net: {net}")
                else:
                    edge_wt = 2 ^ wt_index
                    logger.error(f"no existing weights using dummy weights: {edge_wt}")
                if net not in circuit_graph:
                    logger.debug(f"Adding net node: {net}")
                    if net in inout_ports:
                        circuit_graph.add_node(net, inst_type="net", net_type="external")
                    else:
                        circuit_graph.add_node(net, inst_type="net", net_type="internal")
                elif circuit_graph.has_edge(node["inst"], net):
                    node_name = node["inst"]
                    edge_wt = edge_wt + circuit_graph.get_edge_data(
                        node_name, net)['weight']
                    logger.debug(
                        f"Multiple connection b/w net and node: {net}, {node_name}. new weight: {edge_wt}")
                else:
                    logger.debug(f"New connection found b/w nod {node['inst']}, and net {net}")
                circuit_graph.add_edge(node["inst"], net, weight=edge_wt)
                logger.debug(f"added edge with weight: {edge_wt}")

        logger.debug(
            f"Created bipartitie graph with Total no of Nodes: {len(circuit_graph)} edges: {circuit_graph.number_of_edges()}")

        return circuit_graph
