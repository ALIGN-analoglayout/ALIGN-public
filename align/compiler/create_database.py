#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 10:38:14 2021

@author: kunal001
"""
from email import generator
from operator import sub
from align.schema.types import set_context
from ..schema.subcircuit import SubCircuit
from ..schema import constraint
from ..primitive import main

import logging


logger = logging.getLogger(__name__)


class CreateDatabase:
    def __init__(self, ckt_parser, const_parse):
        self.const_parse = const_parse
        self.ckt_parser = ckt_parser
        self.lib = ckt_parser.library
        self.circuit = ckt_parser.circuit
        self.multi_param_instantiation = list()
        self.remove_redundant_models()
        self.add_user_const()

    def read_inputs(self, name: str):
        """
        Add user constraints to the design
        """
        subckt = self.lib.find(name.upper())
        assert subckt, f"{name.upper()} not found in library {[e.name for e in self.lib]}"
        logger.debug(f"creating database for {subckt}")
        if self.circuit.parameters:
            self.resolve_parameters(name, self.circuit.parameters)
        else:
            self.resolve_parameters(name, subckt.parameters)
        self._update_leaf_instances()
        pwr, gnd, clk = self._get_pgc(subckt)
        self._propagate_power_ports(subckt, pwr, gnd, clk)
        self.propagate_const_top_to_bottom(name, {name})
        return self.lib

    def add_generators(self, pdk_dir):
        for subckt in self.lib:
            if isinstance(subckt, SubCircuit):
                if main.get_generator(subckt.name, pdk_dir) and not subckt.generator:
                    logger.debug(f"available generator for this subcircuit {subckt.name} in PDK ")
                    subckt.add_generator(subckt.name)
                    if [True for const in subckt.constraints if isinstance(const, constraint.Generator)]:
                        logger.debug(f"already available generator for {subckt.name}")
                    else:
                        with set_context(subckt.constraints):
                            subckt.constraints.append(constraint.Generator(name=subckt.name))
                        logger.debug(f"adding generator for {subckt.name}")


    def add_user_const(self):
        for subckt in self.lib:
            if isinstance(subckt, SubCircuit):
                self.const_parse.annotate_user_constraints(subckt)

    def propagate_const_top_to_bottom(self, top_name, traversed):
        top = self.lib.find(top_name)
        all_subckt = {inst.model for inst in top.elements if isinstance(self.lib.find(inst.model), SubCircuit)}
        all_subckt = all_subckt - traversed
        if not all_subckt:
            return
        for const in top.constraints:
            global_const = [constraint.ConfigureCompiler,
                            constraint.DoNotUseLib,
                            ]

            if any(isinstance(const, x) for x in global_const):
                for child in all_subckt:
                    child_const = self.lib.find(child).constraints
                    if const not in child_const and const.propagate:
                        with set_context(child_const):
                            child_const.append(const)
        traversed.update(all_subckt)
        for child in all_subckt:
            self.propagate_const_top_to_bottom(child, traversed)

    def remove_redundant_models(self):
        _model_list = list()
        for subckt in self.lib:
            if isinstance(subckt, SubCircuit):
                for ele in subckt.elements:
                    _model_list.append(ele.model)
        _redundant_list = list()
        for model in self.lib:
            if not isinstance(model, SubCircuit):
                if not (model.name in _model_list or model.base == None):
                    _redundant_list.append(model)
        # Keep base models
        # Delete unused models
        for model in _redundant_list:
            self.lib.remove(model)

    def resolve_parameters(self, name, param):
        subckt = self.lib.find(name.upper())
        assert subckt, f"No subckt found with name: {name}"
        assert isinstance(subckt, SubCircuit), f"{subckt.name} is not a subcircuit"
        logger.debug(
            f"Resolving subckt {name} param {subckt.parameters} with {param} "
        )

        if name.upper() in self.multi_param_instantiation:
            # Second time instantiation of this circuit with same parameters
            if all(v == param[p] for p, v in subckt.parameters.items() if p in param):
                self.multi_param_instantiation.append(name.upper())
                logger.debug(f"Same parameters found {param} {subckt.parameters}")
                return name.upper()
            # Second time instantiation of this circuit with different parameters
            new_name, updated_param = self._find_new_inst_name(subckt, param)
            if new_name == subckt.name or self.lib.find(new_name):
                logger.debug(
                    f"Second similar instance found of module {new_name},{self.multi_param_instantiation}"
                )
            else:
                logger.debug(
                    f"New instance found of {name}, assigning name {new_name}"
                )
                self.multi_param_instantiation.append(new_name)
                with set_context(self.lib):
                    subckt_new = SubCircuit(
                        name=new_name,
                        pins=subckt.pins,
                        parameters=updated_param,
                        constraints=subckt.constraints,
                        generator = subckt.generator
                    )
                assert (
                    self.lib.find(new_name) is None
                ), f"Redefining subckt with name {new_name}"
                self.lib.append(subckt_new)
                with set_context(subckt_new.elements):
                    for ele in subckt.elements:
                        subckt_new.elements.append(ele.copy())
                self._update_instances(subckt_new)
            return new_name
        else:
            self.multi_param_instantiation.append(name.upper())
            logger.debug(
                f"New subckt definition found {subckt.name} {subckt.parameters}"
            )
            for p in subckt.parameters.keys():
                if p in param:
                    subckt.parameters[p] = param[p]
            self._update_instances(subckt)
            return name.upper()

    def _update_instances(self, subckt):
        logger.debug(
            f"Updating instance parameters of subckt {subckt.name} as {subckt.parameters}"
        )
        for inst in subckt.elements:
            if isinstance(self.lib.find(inst.model.upper()), SubCircuit):
                logger.debug(f"checking subckt inst {inst.name} {inst.parameters}")
                for p, v in inst.parameters.items():
                    if v in self.circuit.parameters.keys():
                        inst.parameters[p] = self.circuit.parameters[v]
                    elif v in subckt.parameters:
                        if subckt.parameters[v] in self.circuit.parameters:
                            inst.parameters[p] = self.circuit.parameters[subckt.parameters[v]]
                        else:
                            inst.parameters[p] = subckt.parameters[v]
                new_name = self.resolve_parameters(inst.model.upper(), inst.parameters)
                logger.debug(f"New model name of instance {inst.name} is {new_name}")
                assert self.lib.find(new_name), f"Model {new_name} not found"
                subckt.update_element(inst.name, {"model": new_name})
                assert (
                    subckt.get_element(inst.name).model == new_name
                ), f"New_model {new_name} inst: {inst}"

    def _update_leaf_instances(self):
        for subckt in self.lib:
            if isinstance(subckt, SubCircuit):
                for inst in subckt.elements:
                    # logger.debug(
                    #     f"Updating leaf instance parameters of module \
                    # {subckt.name} as {subckt.parameters}, \
                    # global {self.circuit.parameters}, inst param {inst.parameters}"
                    # )
                    for p, v in inst.parameters.items():
                        if v in self.circuit.parameters.keys():
                            inst.parameters[p] = self.circuit.parameters[v]
                        elif v in subckt.parameters.keys():
                            inst.parameters[p] = subckt.parameters[v]

    def _find_new_inst_name(self, subckt, param, counter=1):
        name = f"{subckt.name.upper()}_{counter}"
        _ckt = self.lib.find(name)
        new_param = subckt.parameters.copy()
        for p in new_param.keys():
            if p in param.keys():
                new_param[p] = param[p]
        if _ckt:
            duplicate = True
            if (
                subckt.pins == _ckt.pins
                and new_param == _ckt.parameters
                and subckt.constraints == _ckt.constraints
                and subckt.generator == _ckt.generator
            ):
                logger.debug(f"Existing ckt defnition found, checking all elements")
                for x in subckt.elements:
                    if (
                        (_ckt.get_element(x.name).model == x.model)
                        and (_ckt.get_element(x.name).parameters == x.parameters)
                        and (_ckt.get_element(x.name).pins == x.pins)
                    ):
                        continue
                    else:
                        duplicate = False
                        break  # Break after first mismatch
            else:
                duplicate = False
            if duplicate == False:
                logger.debug(
                    f"Multiple different sized instance of subcircuit found {subckt.name} count {counter+1}"
                )
                name, new_param = self._find_new_inst_name(subckt, param, counter + 1)
        return name, new_param

    def _get_pgc(self, subckt):
        pwr = list()
        gnd = list()
        clk = list()
        for const in subckt.constraints:
            if isinstance(const, constraint.PowerPorts):
                pwr.extend(const.ports)
            elif isinstance(const, constraint.GroundPorts):
                gnd.extend(const.ports)
            elif isinstance(const, constraint.ClockPorts):
                clk.extend(const.ports)
        return pwr, gnd, clk

    def _propagate_power_ports(self, subckt, pwr, gnd, clk):
        pwr_child, gnd_child, clk_child = self._get_pgc(subckt)
        if not pwr_child and pwr:
            pwr_child = pwr
            subckt.constraints.append(constraint.PowerPorts(ports=pwr_child))
        elif pwr_child:
            diff = list(set(pwr).difference(pwr_child))
            pwr_child.extend(diff)
            for const in subckt.constraints:
                if isinstance(const, constraint.PowerPorts):
                    const.ports.extend(diff)

        if not gnd_child and gnd:
            gnd_child = gnd
            subckt.constraints.append(constraint.GroundPorts(ports=gnd_child))
        elif gnd_child:
            diff = list(set(gnd).difference(gnd_child))
            gnd_child.extend(diff)
            for const in subckt.constraints:
                if isinstance(const, constraint.GroundPorts):
                    const.ports.extend(diff)

        if not clk_child and clk:
            clk_child = clk
            subckt.constraints.append(constraint.ClockPorts(ports=clk_child))
        elif clk_child:
            diff = list(set(clk).difference(clk_child))
            clk_child.extend(diff)
            for const in subckt.constraints:
                if isinstance(const, constraint.ClockPorts):
                    const.ports.extend(diff)
        for inst in subckt.elements:
            inst_subckt = self.lib.find(inst.model)
            if isinstance(inst_subckt, SubCircuit):
                pp = [p for p, c in inst.pins.items() if c in pwr_child]
                gp = [p for p, c in inst.pins.items() if c in gnd_child]
                gc = [p for p, c in inst.pins.items() if c in clk_child]
                self._propagate_power_ports(inst_subckt, list(pp), list(gp), list(gc))
