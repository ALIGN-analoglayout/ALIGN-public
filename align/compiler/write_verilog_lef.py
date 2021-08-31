# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
from align.schema.subcircuit import SubCircuit

import logging
logger = logging.getLogger(__name__)


class WriteVerilog:
    """ write hierarchical verilog file """
    def __init__(self, ckt, ckt_data, power_pins):
        self.ckt_data = ckt_data
        self.circuit_name = ckt.name
        self.pins = ckt.pins
        self.power_pins = power_pins

        self.subckt_data = self.ckt_data.find(ckt.name)
        self.constraints = self.ckt_data.find(ckt.name).constraints

    def gen_dict( self):
        d = {}
        d['name'] = self.circuit_name
        d['parameters'] = self.pins
        d['constraints'] = self.constraints.dict()['__root__']
        d['instances'] = []

        for ele in self.subckt_data.elements:
            instance = {}
            instance['template_name'] = ele.abstract_name
            instance['instance_name'] = ele.name
            instance['fa_map']= self.gen_dict_fa(ele.pins.keys(), ele.pins.values())
            d['instances'].append( instance)

        return d

    def gen_dict_fa(self, a, b):
        if len(a) == len(b):
            mapped_pins = []
            for ai, bi in zip(a, b):
                mapped_pins.append( { "formal" : ai, "actual" : bi})
            return list(sorted(mapped_pins,key=lambda x:x['formal']))
        elif len(set(a)) == len(set(b)):
            if len(a) > len(b):
                mapped_pins = []
                check_short = []
                no_of_short = 0
                for i in range(len(a)):
                    if a[i] in check_short:
                        mapped_pins.append(mapped_pins[check_short.index(a[i])])
                        no_of_short += 1
                    else:
                        mapped_pins.append( { "formal" : a[i], "actual": b[i - no_of_short]})
                        check_short.append(a[i])
                return list(sorted(mapped_pins,key=lambda x:x['formal']))
        else:
            logger.error( f"unmatched ports found: {a} {b}")
            assert False


