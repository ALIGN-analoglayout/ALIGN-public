# -*- coding: utf-8 -*-
"""
Created on Wed Feb 2 13:12:15 2022

@author: kunal
"""

from align.schema.types import set_context
import logging
import hashlib

from align.schema import SubCircuit, Model, constraint

logger = logging.getLogger(__name__)


def gen_key(param):
    skeys = sorted(param.keys())
    arg_str = '_'.join([k+':'+str(param[k]) for k in skeys])
    block_arg = f"_{str(int(hashlib.sha256(arg_str.encode('utf-8')).hexdigest(), 16) % 10**8)}"
    return block_arg


def create_subckt(element, name, lib, pins):
    if not lib.find(name):  # add subckt in primitive library if not already existing
        with set_context(lib):
            new_subckt = SubCircuit(name=name, pins=pins)
        with set_context(new_subckt.elements):
            new_subckt.elements.append(element)
        lib.append(new_subckt)

def gen_primitive_def(element, primitive_library):
    lib = element.parent.parent.parent
    ckt = element.parent.parent
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
        block_arg = gen_key(element.parameters)
        unique_name = f'{model}{block_arg}'
        create_subckt(element, unique_name, plib, list(element.pins.keys()))
    else:
        assert False, f"No definition found for instance {element} in {element.name}"
    if unique_name:
        element.add_abs_name(unique_name)


