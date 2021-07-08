# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
from math import sqrt, ceil,floor

from .util import convert_to_unit
from ..primitive import generate_primitive_lef

import logging
logger = logging.getLogger(__name__)

from copy import deepcopy

class WriteVerilog:
    """ write hierarchical verilog file """
    def __init__(self, circuit_name, inout_pin_names, hier_graph_dict, power_pins):
        self.hier_graph_dict = hier_graph_dict
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = []
        for port in sorted(inout_pin_names):
            if port not in power_pins:
                self.pins.append(port)
        self.power_pins=power_pins

        self.circuit_graph = self.hier_graph_dict[self.circuit_name].graph
        self.constraints = self.hier_graph_dict[self.circuit_name].constraints

    def gen_dict( self):
        d = {}
        d['name'] = self.circuit_name
        d['parameters'] = self.pins
        d['constraints'] = self.constraints.dict()['__root__']
        d['instances'] = []

        for node, attr in self.circuit_graph.nodes(data=True):


            if 'source' in attr['inst_type']:
                logger.debug(f"Skipping source nodes : {node}")
                continue
            if 'net' not in attr['inst_type']:
                logger.debug(f"Writing node: {node} {attr}")

                instance = {}

                instance['template_name'] = attr['inst_type']
                instance['instance_name'] = node

                ports = []
                nets = []
                if "ports_match" in attr:
                    logger.debug(f'Nets connected to ports: {attr["ports_match"]}')
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
                    if 'Switch_NMOS_G' in attr['inst_type']:
                        ports.append('B')
                        nets.append(nets[1])
                    elif 'Switch_PMOS_G' in attr['inst_type']:
                        ports.append('B')
                        nets.append(nets[1])
                elif "connection" in attr and attr["connection"]:
                    for key, value in attr["connection"].items():
                        if attr['inst_type'] in self.hier_graph_dict and key in self.hier_graph_dict[attr['inst_type']]['ports']:
                            ports.append(key)
                            nets.append(value)
                else:
                    logger.error(f"No connectivity info found for block {d['name']}: {', '.join(attr['ports'])}")
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                instance['fa_map'] = self.gen_dict_fa(ports, nets)
                if not instance['fa_map']:
                    logger.warning(f"Unconnected module, only power/gnd conenction found {node}")

                d['instances'].append( instance)

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


def generate_lef(name:str, attr:dict, available_block_lef:list, design_config:dict, uniform_height=False):
     block_name, block_args = generate_primitive_lef(name, attr, available_block_lef, design_config, uniform_height)
     #generate_lef(lef_name, attr, primitives, design_config, uniform_height)
     return block_name, block_args 
