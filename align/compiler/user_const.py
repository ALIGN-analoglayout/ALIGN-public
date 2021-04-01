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

class ConstraintParser:
    def __init__(self, pdk_dir: pathlib.Path, input_dir: pathlib.Path):
        self.input_dir = input_dir
        self.known_types = {
            'int':int,
            'str':str,
            'list':list
            }
        with open(pdk_dir / 'layers.json',"rt") as fp:
            pdk_info = json.load(fp)
            self.valid_const =pdk_info["valid_constraints"]
        
    def read_user_const(self, design_name: str):
        """
        Reads user defined constraints and create a dictionary for each hierarchy
  
        """
        self.block_const = {}
        fp = self.input_dir / (design_name+'.const')
        fp_json = self.input_dir / (design_name+'.const.json')
        if fp_json.is_file():
            logger.info(f"JSON input const file for block {design_name} {fp_json}")
            f = open(fp_json, "r")
            self.block_const = json.load(f)
        elif fp.is_file():
            logger.info(f"CMD-line input const file for block {design_name}")
            all_const = []
            f = open(fp, "r")
            for line in f:
                if not line.strip():
                    continue
                a = line.strip().split('-')
                const = {}
                const["const_name"] = a[0].strip()
                for x in a[1:]:
                    arg = x.split()[0]
                    value =  ''.join(x.split()[1:])
                    const[arg]=value
                const = self._translate_valid_const(const)
                if const:
                    all_const.append(const)
            self.block_const['constraints'] = all_const
        else:
            logger.info(f"No user constraints found for block {design_name} in path {self.input_dir}")
            return None
        self._map_valid_const()
        return self.block_const
            
    
    def _translate_valid_const(self,const:dict):
        """
        Read line parameters as dictionary element
    
        Parameters
        ----------
        const : dict
            constraint from line.
    
        Returns
        -------
        const : dict
            modified dictionary.
    
        """
        
        logger.debug(f"checking constraint {const}")
        if const["const_name"] not in self.valid_const:
            logger.warning(f"ignoring invalid constraint {const} ")
            return None
        valid_arg = self.valid_const[const["const_name"]]
        if 'blocks' in const:
            const['blocks'] = const["blocks"].replace(']','').replace('[','').split(',')
            self._check_type(const['blocks'],valid_arg['blocks'])
        if 'nets' in const:
            const['nets'] = const["nets"].replace(']','').replace('[','').split(',')
            self._check_type(const['nets'],valid_arg['nets'])
        if 'pins1' in const:
            const['pins1'] = const["pins1"].replace(']','').replace('[','').split(',')
            self._check_type(const['pins1'],valid_arg['pins2'])
        if 'pins2' in const:
            const['pins2'] = const["pins2"].replace(']','').replace('[','').split(',')
            self._check_type(const['pins2'],valid_arg['pins2'])
        if 'ports' in const:
            const['ports'] = const["ports"].replace(']','').replace('[','').split(',')
            self._check_type(const['ports'],valid_arg['ports'])
        if 'pairs' in const:
            groups=[]
            for blocks in const["pairs"].split('],'):
                groups.append(blocks.replace(']','').replace('[','').split(','))
            const['pairs'] =  groups
            self._check_type(const['pairs'],valid_arg['pairs'])
        if 'name' in const:
            self._check_type(const['name'],valid_arg['name'])
        if 'net1' in const:
            self._check_type(const['net1'],valid_arg['net1'])
        if 'net2' in const:
            self._check_type(const['net2'],valid_arg['net2'])
        if 'style' in const:
            self._check_type(const['style'],valid_arg['style'])
        if 'abs_distance' in const:
            const['abs_distance']=int(const['abs_distance'])
        if 'criticality' in const:
            const['abs_distance'] = int(const['criticality'])
        if 'multiplier' in const:
            const['multiplier'] = int(const['multiplier'])
        if 'weight' in const:
            const['weight'] = int(const['weight'])
        if 'direction' in const:
            self._check_type(const['direction'],valid_arg['direction'])
        if 'location' in const:
            self._check_type(const['location'],valid_arg['location'])
        if 'unit_cap' in const:
            self._check_type(const['unit_cap'],valid_arg['unit_cap'])
        if 'shield' in const:
            self._check_type(const['shield'],valid_arg['shield'])   
        if 'num_units' in const:
            const['num_units'] = [int(x) for x in const["num_units"].replace(']','').replace('[','').split(',')]
            self._check_type(const['num_units'],valid_arg['num_units'])  
        if 'dummy' in const:
            const['dummy'] = (const['dummy']==True)
        return const
    def _check_type(self,data,arg):
        if isinstance(arg,list):
            assert data in arg
        elif arg in self.known_types:
            data_type = self.known_types[arg]
            assert isinstance(data, data_type), f"{type(data)},{data_type}"
        else:
            logger.warning(f"wrong data type in constraint: {data}, valid types are: {arg}" )            
        
    def _resolve_alias(self,all_const:list):
    
        #Find alias
        map_alias ={}
        for const in all_const:
            if const["const_name"] == 'CreateAlias':
                map_alias[const["name"]]=const["blocks"]
        all_const = [i for i in all_const if not i['const_name']=='CreateAlias']
        #Replace nested alias
        if not map_alias:
            return all_const
        for blocks in map_alias.values():
            for i,block in enumerate(blocks):
                if block in map_alias:
                    blocks[i]=map_alias[block]
        
        for const in all_const:
            if 'blocks' in const: 
               self._replace_alias(const["blocks"],map_alias)
            elif 'nets' in const:
               self._replace_alias(const["nets"],map_alias)
            elif 'pins1' in const:
               self._replace_alias(const["pins1"],map_alias)
            elif 'pins2' in const:  
               self._replace_alias(const["pins2"],map_alias)
            elif 'ports' in const:  
               self._replace_alias(const["ports"],map_alias)
            elif 'pairs' in const:
                for ele in const['pairs']:
                    if isinstance(ele, str):
                        self._replace_alias(ele, map_alias)
        return all_const
        
    def _replace_alias(self,blocks:list,map_alias:dict):
        """
        Replace alias names with the list by concatenating them

        Parameters
        ----------
        blocks : list
            list of names/blocks to be replaced.
        map_alias : dict
            alias name to block mapping.

        Returns
        -------
        None.

        """
        for i in range(len(blocks)):
            if blocks[i] in map_alias:
                name = blocks.pop(i)
                blocks.extend(map_alias[name])
        
    def _map_valid_const(self):
        """
        Maps input format to pnr format

        """
        all_const = self.block_const["constraints"]
        all_const = self._resolve_alias(all_const)
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
        self.block_const["constraints"] = [i for i in all_const if not i['const_name'] == 'NetConst' \
                                            and not i['const_name'] == 'PortLocation'\
                                            and not  i['const_name'] == 'MultiConnection']
        self.block_const["constraints"].extend(added_const)
        logger.info(f"Const mapped to PnR const format {self.block_const['constraints']}")
    
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


