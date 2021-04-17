#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Jan 13 14:50:24 2021

@author: kunal001
"""
import pathlib
import pprint
import json
import logging

logger = logging.getLogger(__name__)
pp = pprint.PrettyPrinter(indent=4)

class ConstraintWriter:
    def __init__(self, pdk_dir: pathlib.Path):
        self.known_types = {
            'int':int,
            'str':str,
            'list':list
            }
        with open(pdk_dir / 'layers.json',"rt") as fp:
            pdk_info = json.load(fp)
            self.valid_const = pdk_info["valid_constraints"]

    def map_valid_const(self,block_const):
        """
        Maps input format to pnr format

        """
        all_const = block_const["constraints"]
        logger.info(f"input constraints {all_const}")
        #Start mapping
        added_const=[]
        for const in all_const:
            if const["const_name"] == 'OrderBlocks':
                const["const_name"] = 'Ordering'
            elif const["const_name"] == 'MatchBlocks':
                const["const_name"] = 'MatchBlock'
                const['block1'] =  const['blocks'][0]
                const['block2'] =  const['blocks'][1]
                del const['blocks']
            elif const["const_name"] == 'BlockDistance':
                const["const_name"] = 'bias_graph'
                const["distance"] = const.pop('abs_distance')               
            elif const["const_name"] == 'HorizontalDistance':
                const["const_name"] = 'bias_Hgraph'
                const["distance"] = const.pop('abs_distance')
            elif const["const_name"] == 'VerticalDistance':
                const["const_name"] = 'bias_Vgraph'
                const["distance"] = const.pop('abs_distance')
            elif const["const_name"] == 'AspectRatio':
                const["const_name"] = 'Aspect_Ratio'
            elif const["const_name"] == 'SymmetricBlocks':
                const["const_name"] = 'SymmBlock'
                const["axis_dir"] = const.pop("direction")
                pairs = []
                for blocks in const["pairs"]:
                    if len(blocks)==1:
                        temp = {
                            "type": "selfsym",
                            "block": blocks[0]
                            }
                    elif len(blocks)==2:
                        temp = {
                            "type":"sympair",
                            "block1":blocks[0],
                            "block2":blocks[1]
                            }
                    else:
                        logger.warning(f"invalid group for symmetry {blocks}")
                    pairs.append(temp)
                const["pairs"] = pairs
            elif const["const_name"] == 'GroupCaps':
                const["const_name"] = 'CC'
                const["cap_name"] = const.pop("name")
                const["unit_capacitor"] = const.pop("unit_cap")
                const["size"] = const.pop("num_units")
                const["nodummy"] = not const["dummy"]
                del const["dummy"]
            elif const["const_name"] == 'AlignBlocks':
                const["const_name"] = 'AlignBlock'
            elif const["const_name"] == 'SymmetricNets':
                const["const_name"] = 'SymmNet'
                const["axis_dir"] = const.pop("direction")
                if "pins1" in const and "pins2" in const:
                    pins1 = self._map_pins(const["pins1"])
                    pins2 = self._map_pins(const["pins2"])
                    del const["pins1"]
                    del const["pins2"]
                else:
                    pins1 = [{"type": "dummy", "name": "dummy", "pin": None}]
                    pins2 = [{"type": "dummy", "name": "dummy", "pin": None}]
                const['net1'] = {
                    "name": const['net1'],
                    "blocks": pins1}
                const['net2'] = {
                    "name": const['net2'],
                    "blocks": pins2}
            elif const["const_name"] == 'PortLocation':
                for port in const["ports"]:
                    extra = {
                        "const_name" : 'PortLocation',
                        "location" : const["location"],
                        "terminal_name" : port
                    }
                    added_const.append(extra)
            elif const["const_name"] == 'MultiConnection':
                for net in const["nets"]:
                    extra = {
                        "const_name" : 'Multi_Connection',
                        "multi_number" : int(const["multiplier"]),
                        "net_name" : net
                    }
                    added_const.append(extra)
            elif const["const_name"] == 'NetConst':
                for net in const["nets"]:
                    if 'shield' in const and 'criticality' in const and not const['shield'] =="None":
                        extra = {
                            "const_name" : 'ShieldNet',
                            "net_name" : net,
                            "shield_net" : const["shield"]
                            }
                        added_const.append(extra)
                        extra = {
                            "const_name" : 'CritNet',
                            "net_name" : net,
                            "priority" : const["criticality"]
                            }
                        added_const.append(extra)
                    elif 'shield' in const and not const['shield'] =="None":
                        extra = {
                            "const_name" : 'ShieldNet',
                            "net_name" : net,
                            "shield_net" : const["shield"]
                            }
                        added_const.append(extra)
    
                    elif 'criticality' in const and const['shield'] =="None":
                        extra = {
                            "const_name" : 'CritNet',
                            "net_name" : net,
                            "priority" : const["criticality"]
                            }
                        added_const.append(extra)
        block_const["constraints"] = [i for i in all_const if not i['const_name'] == 'NetConst' \
                                            and not i['const_name'] == 'PortLocation'\
                                            and not  i['const_name'] == 'MultiConnection']
        block_const["constraints"].extend(added_const)
        logger.info(f"Const mapped to PnR const format {block_const['constraints']}")
        return block_const

    def _check_type(self,data,arg):
        if isinstance(arg,list):
            assert data in arg
        elif arg in self.known_types:
            data_type = self.known_types[arg]
            assert isinstance(data, data_type), f"{type(data)},{data_type}"
        else:
            logger.warning(f"wrong data type in constraint: {data}, valid types are: {arg}" )            
        

    def _map_pins(self,pins:list):
        blocks=[]
        for pin in pins:
            if '/' in pin:
                temp = {
                    "type":"pin",
                    "name":pin.split('/')[0],
                    "pin":pin.split('/')[1]
                    }
            else:
                temp = {
                    "type":"terminal",
                    "name":pin, 
                    "pin":None
                    }
            blocks.append(temp)
        return blocks


