#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 10:38:14 2021

@author: kunal001
"""
from align.schema import constraint, model
from align.schema.types import set_context
from networkx.algorithms.shortest_paths.weighted import multi_source_dijkstra
from ..schema.subcircuit import SubCircuit
from ..schema.instance import Instance

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
        subckt = self.ckt_parser.library.find(name)
        assert subckt, f"Design {name} not found in library {[e.name for e in self.ckt_parser.library]}"
        self.const_parse.annotate_user_constraints(subckt)
        logger.debug(f"creating database for {subckt}")
        for pin in subckt.pins:
            assert pin in subckt.nets, f"Floating pin: {pin} found for subckt {subckt.name}"
        self.resolve_parameters(name, subckt.parameters)
        #TODO remove redundant library model
        return self.ckt_parser.library
    def resolve_parameters(self, name, param):
        subckt = self.ckt_parser.library.find(name)
        if not isinstance(subckt, SubCircuit):
            return
        if name in self.multi_param_instantiation:
            #Second time instantiation of this circuit with same parameters
            if all(v==param[p] for p,v in subckt.parameters if p in param):
                return
            #Second time instantiation of this circuit with different parameters
            new_name = self.model_instance(subckt)
            with set_context(self.ckt_parser):
                subckt_new = SubCircuit(name=new_name,
                                pins=subckt.pins,
                                parameters=subckt.parameters,
                                constraints=subckt.constraints,
                                elements = subckt.elements)
                self.ckt_parser.append(subckt_new)
            subckt = subckt_new
        logger.debug(f"resolving subckt {name} parameters {param} default values: {subckt.parameters}")
        for p,v in subckt.parameters.items():
            if p in param:
                subckt.parameters[p]=param[p]
        for inst in subckt.elements:
            for p,v in inst.parameters.items():
                if v in subckt.parameters:
                    inst.parameters[p]=subckt.parameters[v]
            self.resolve_parameters(inst.model, inst.parameters)

    def model_instance(self, subckt, counter=0):
        if counter == 0:
            name = subckt.name
        else:
            name = f'{subckt.name}_{counter}'
        existing_ckt = self.subckt.parent.find(name)
        if existing_ckt:
            if subckt.pins == existing_ckt.pins and \
                subckt.parameters == existing_ckt.parameters and \
                subckt.constraints == existing_ckt.constraints:
                # logger.debug(f"Existing ckt defnition found, checking all elements")
                for x in subckt.elements:
                    if (not existing_ckt.get_element(x.name).model == x.model) or \
                        (not existing_ckt.get_element(x.name).parameters == x.parameters) or \
                            (not existing_ckt.get_element(x.name).pins == x.pins):
                        logger.info(f"multiple instance of same subcircuit found {subckt.name} {counter+1}")
                        name = self.instance_counter(subckt,counter+1)
                        break #Break after first mismatch
        return name

    def create_subckt_instance(self, subckt, match, instance_name):
        with set_context(self.subckt.parent):
            subckt_instance = SubCircuit(name=instance_name,
                                pins=subckt.pins,
                                parameters=subckt.parameters,
                                constraints=subckt.constraints,
                                elements = subckt.elements)
        return subckt_instance




