# -*- coding: utf-8 -*-
"""
Created on Wed Feb 2 13:12:15 2022

@author: kunal
"""
import pathlib
from align.schema.types import set_context
import logging
import hashlib
import json

from align.schema import SubCircuit, Model, constraint, Library

logger = logging.getLogger(__name__)


def gen_key(param):
    skeys = sorted(param.keys())
    arg_str = '_'.join([k+':'+str(param[k]) for k in skeys])
    block_arg = f"_{str(int(hashlib.sha256(arg_str.encode('utf-8')).hexdigest(), 16) % 10**8)}"
    return block_arg


def create_subckt(element, name, lib, pins):
    with set_context(lib):
        new_subckt = SubCircuit(name=name, pins=pins)
    with set_context(new_subckt.elements):
        new_subckt.elements.append(element)
    check = lib.find(name)

    if not check:  # add subckt in primitive library if not already existing
        lib.append(new_subckt)


def gen_primitive_def(element, primitive_library):
    lib = element.parent.parent.parent
    plib = primitive_library
    model = element.model

    generator = lib.find(element.generator)
    if isinstance(generator, SubCircuit):
        gen_const = [True for const in generator.constraints if isinstance(const, constraint.Generator)]
        unique_name = model
        if gen_const:
            with set_context(plib):
                plib.append(generator)
    elif generator is None or isinstance(generator, Model): #base model or model
        # just using parameters as pins are unique corresponding to a model
        block_arg = gen_key(element.parameters)
        unique_name = f'{model}{block_arg}'
        create_subckt(element, unique_name, plib, list(element.pins.keys()))
        assert plib.find(unique_name)
    else:
        assert False, f"No definition found for instance {element} in {element.name}"
    if unique_name:
        element.add_abs_name(unique_name)


def gen_primitive_collateral(ckt_data: Library):
    """
    create a unique name for each instance and
    create a subcircuit for all instance for feeding to primitive generator

    Args:
        ckt_data ([type]): ckt library after annotation
    Returns:
        primitives: library of primitives
    """
    primitives = Library(loadbuiltins=True)
    for ckt in ckt_data:
        if not isinstance(ckt, SubCircuit):
            continue
        elif [True for const in ckt.constraints if isinstance(const, constraint.Generator)]:
            continue
        logger.debug(f"Found module: {ckt.name} {ckt.elements} {ckt.pins}")
        group_cap_instances = []
        for const in ckt.constraints:
            if isinstance(const, constraint.GroupCaps):
                group_cap_instances.append(const.name.upper())

        for ele in ckt.elements:
            if ele.name in group_cap_instances:
                ele.add_abs_name(ele.model)
            else:
                gen_primitive_def(ele, primitives)

    return primitives
