# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
from align.schema import model
from math import sqrt, ceil,floor

from .util import convert_to_unit
# from .merge_nodes import merge_subckt_param
from align.schema.subcircuit import SubCircuit

import logging
logger = logging.getLogger(__name__)

from copy import deepcopy

class WriteVerilog:
    """ write hierarchical verilog file """
    def __init__(self, ckt, ckt_data, power_pins):
        self.ckt_data = ckt_data
        self.circuit_name = ckt.name
        self.inout_pins = ckt.pins
        self.pins = []
        for port in sorted(ckt.pins):
            if port not in power_pins:
                self.pins.append(port)
        self.power_pins=power_pins

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
            print(ele)
            instance['template_name'] = ele.model
            if ele.model in self.ckt_data:
                print(self.ckt_data.find(ele.model))
            instance['instance_name'] = ele.name
            instance['fa_map']= self.gen_dict_fa(ele.pins.keys(), ele.pins.values())
            d['instances'].append( instance)

        #         instance['fa_map'] = self.gen_dict_fa(ports, nets)
        #         if not instance['fa_map']:
        #             logger.warning(f"Unconnected module, only power/gnd conenction found {node}")

        #         d['instances'].append( instance)


        return d

    def gen_dict_fa(self, a, b):
        if len(a) == len(b):
            mapped_pins = []
            for ai, bi in zip(a, b):
                if ai not in self.power_pins:
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
                mapped_pins = [x for x in mapped_pins if x['formal'] not in self.power_pins]

                return list(sorted(mapped_pins,key=lambda x:x['formal']))

        else:
            logger.error( f"unmatched ports found: {a} {b}")
            assert False

def write_verilog( j, ofp):

    for module in j['modules']:
        print( f"module {module['name']} ( {', '.join( module['parameters'])} );", file=ofp)
        print( f"input {', '.join( module['parameters'])};", file=ofp)
        print( file=ofp)
        for instance in module['instances']:
            pl = ', '.join( f".{fa['formal']}({fa['actual']})" for fa in instance['fa_map'])
            tn = instance['template_name'] if 'template_name' in instance else instance['abstract_template_name']

            print( f"{tn} {instance['instance_name']} ( {pl} );", file=ofp)

        print( file=ofp)
        print( 'endmodule', file=ofp)

    if 'global_signals' in j and j['global_signals']:
        prefixes = set()
        for s in j['global_signals']:
            prefixes.add( s['prefix'])
        assert 1 == len(prefixes)
        prefix = list(prefixes)[0]
        print( file=ofp)
        print( "`celldefine", file=ofp)
        print( f"module {prefix};", file=ofp)
        for s in j['global_signals']:
            formal, actual = s['formal'], s['actual']
            print( f'{formal} {actual};', file=ofp)
        print( "endmodule", file=ofp)
        print( "`endcelldefine", file=ofp)


