#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 10:38:14 2021

@author: kunal001
"""
from align.schema.instance import Instance
from align.schema.types import set_context
from networkx.algorithms.shortest_paths.weighted import multi_source_dijkstra
from ..schema.subcircuit import SubCircuit

import logging
logger = logging.getLogger(__name__)


class CreateDatabase:
    def __init__(self, ckt_parser, const_parse):
        self.const_parse = const_parse
        self.ckt_parser = ckt_parser
        self.multi_param_instantiation = []

    def read_inputs(self, name: str):
        """
        Add user constraints to the design
        """
        subckt = self.ckt_parser.library.find(name.upper())
        assert subckt, f"Design {name.upper()} not found in library {[e.name for e in self.ckt_parser.library]}"
        self.const_parse.annotate_user_constraints(subckt)
        logger.debug(f"creating database for {subckt}")
        for pin in subckt.pins:
            assert pin in subckt.nets, f"Floating pin: {pin} found for subckt {subckt.name} nets: {subckt.nets}"
        if self.ckt_parser.circuit.parameters:
            self.resolve_parameters(name, self.ckt_parser.circuit.parameters)
        else:
            self.resolve_parameters(name, subckt.parameters)
        self._update_leaf_instances()
        #TODO Remove redundant models
        return self.ckt_parser.library

    def resolve_parameters(self, name, param):
        subckt = self.ckt_parser.library.find(name.upper())
        assert subckt, f"No subckt found with name: {name}"
        assert isinstance(subckt, SubCircuit), f"subckt {subckt.name} is not a subcircuit"
        logger.debug(f"Resolving subckt {name} parameters {param} default values: {subckt.parameters}")

        if name.upper() in self.multi_param_instantiation:
            #Second time instantiation of this circuit with same parameters
            if all(v==param[p] for p,v in subckt.parameters.items() if p in param):
                self.multi_param_instantiation.append(name.upper())
                logger.debug(f"Same parameters found {param} {subckt.parameters}")
                return name.upper()
            #Second time instantiation of this circuit with different parameters
            new_name,updated_param = self._find_new_inst_name(subckt, param)
            if new_name == subckt.name or self.ckt_parser.library.find(new_name):
                logger.debug(f"Second similar instance found of module {new_name},{self.multi_param_instantiation} ")
            else:
                logger.debug(f"New instance found of module {name} assigning name {new_name}, {self.multi_param_instantiation}")
                self.multi_param_instantiation.append(new_name)
                with set_context(self.ckt_parser.library):
                    subckt_new = SubCircuit(name=new_name,
                                    pins=subckt.pins,
                                    parameters=updated_param,
                                    constraints=subckt.constraints)
                assert self.ckt_parser.library.find(new_name) is None, f"Redefining subckt with name {new_name}"
                self.ckt_parser.library.append(subckt_new)
                with set_context(subckt_new.elements):
                    for ele in subckt.elements:
                        subckt_new.elements.append(ele.copy())
                self._update_instances(subckt_new)
            return new_name
        else:
            self.multi_param_instantiation.append(name.upper())
            logger.debug(f"New subckt definition found {subckt.name} {subckt.parameters}")
            for p in subckt.parameters.keys():
                if p in param:
                    subckt.parameters[p]=param[p]
            self._update_instances(subckt)
            return name.upper()

    def _update_instances(self, subckt):
        logger.debug(f"Updating instance parameters of subckt {subckt.name} as {subckt.parameters}")
        for inst in subckt.elements:
            if isinstance(self.ckt_parser.library.find(inst.model.upper()), SubCircuit):
                logger.debug(f"checking subckt inst {inst.name} {inst.parameters}")
                for p,v in inst.parameters.items():
                    if v in subckt.parameters:
                        inst.parameters[p]=subckt.parameters[v]
                new_name = self.resolve_parameters(inst.model.upper(), inst.parameters)
                logger.debug(f"New model name of instance {inst.name} is {new_name}")
                assert self.ckt_parser.library.find(new_name), f" Model not found in library {new_name}"
                subckt.update_element(inst.name, {'model':new_name})
                assert subckt.get_element(inst.name).model==new_name, f"new_model {new_name} inst: {inst}"

    def _update_leaf_instances(self):
        for subckt in self.ckt_parser.library:
            if isinstance(subckt, SubCircuit):
                for inst in subckt.elements:
                    logger.debug(f"Updating leaf instance parameters of module \
                    {subckt.name} as {subckt.parameters}, global {self.ckt_parser.circuit.parameters}, inst param {inst.parameters} ")
                    for p,v in inst.parameters.items():
                        if v in self.ckt_parser.circuit.parameters.keys():
                            inst.parameters[p] = self.ckt_parser.circuit.parameters[v]
                        elif v in subckt.parameters.keys():
                            inst.parameters[p] = subckt.parameters[v]

    def _find_new_inst_name(self, subckt, param, counter=1):
        name = f'{subckt.name.upper()}_{counter}'
        existing_ckt = self.ckt_parser.library.find(name)
        new_param = subckt.parameters.copy()
        for p in new_param.keys():
            if p in param.keys():
                new_param[p]=param[p]
        if existing_ckt:
            duplicate = True
            if subckt.pins == existing_ckt.pins and \
                new_param == existing_ckt.parameters and \
                subckt.constraints == existing_ckt.constraints:
                logger.debug(f"Existing ckt defnition found, checking all elements")
                for x in subckt.elements:
                    if ( existing_ckt.get_element(x.name).model == x.model) and \
                        ( existing_ckt.get_element(x.name).parameters == x.parameters) and \
                        ( existing_ckt.get_element(x.name).generator == x.generator) and \
                        ( existing_ckt.get_element(x.name).pins == x.pins):
                        continue
                    else:
                        duplicate = False
                        break #Break after first mismatch
            else:
                duplicate = False
            if duplicate == False:
                logger.debug(f"Multiple different sized instance of subcircuit found {subckt.name} count {counter+1}")
                name, new_param = self._find_new_inst_name(subckt, param, counter+1)
        return name, new_param
