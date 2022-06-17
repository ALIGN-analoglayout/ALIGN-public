#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Jan 13 14:50:24 2021

@author: kunal001
"""
import pprint
import logging
from ..schema import constraint
import itertools

logger = logging.getLogger(__name__)
pp = pprint.PrettyPrinter(indent=4)


class PnRConstraintWriter:
    def __init__(self):
        pass

    def map_valid_const(self, all_const):
        """
        Maps input format to pnr format
        """
        logger.debug(f"Input constraints: {all_const}")

        # Start mapping
        pnr_const = []
        for input_const in constraint.expand_user_constraints(all_const):

            # Create dict for PnR constraint and rename constraint to const_name
            const = input_const.dict(exclude={'constraint'}, exclude_unset=False)
            const['const_name'] = input_const.__class__.__name__

            # Rename instances to blocks
            if 'instances' in const:
                const['blocks'] = const['instances']
                del const['instances']

            # Exclude constraints not to be exposed to PnR
            if const['const_name'] in ['DoNotIdentify', 'GroupBlocks', 'DoNotUseLib', 'ConfigureCompiler']:
                continue

            # Exclude constraints that need to be to multiple constraints
            if not const['const_name'] in ('NetPriority', 'NetConst', 'PortLocation', 'MultiConnection', 'PlaceCloser'):
                pnr_const.append(const)

            # Constraint-specific field transformations
            if const["const_name"] == 'Order':
                const["const_name"] = 'Ordering'
                if const["direction"] in ("left_to_right", "horizontal"):
                    const["direction"] = 'H'
                elif const["direction"] in ("top_to_bottom", "vertical"):
                    const["direction"] = 'V'
                else:
                    raise NotImplementedError(f'PnR does not support direction {const["direction"]} yet')

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
                del const['subcircuit']

            elif const["const_name"] == 'Boundary':
                del const['subcircuit']
                for key in ['max_width', 'max_height']:
                    if const[key] is None:
                        del const[key]

            elif const["const_name"] == 'SymmetricBlocks':
                const["const_name"] = 'SymmBlock'
                const["axis_dir"] = const.pop("direction")
                pairs = []
                for blocks in const["pairs"]:
                    if len(blocks) == 1:
                        temp = {"type": "selfsym", "block": blocks[0]}
                    elif len(blocks) == 2:
                        temp = {"type": "sympair", "block1": blocks[0], "block2": blocks[1]}
                    else:
                        logger.warning(f"invalid group for symmetry {blocks}")
                    pairs.append(temp)
                const["pairs"] = pairs

            elif const["const_name"] == 'GroupCaps':
                const["const_name"] = 'CC'
                const["cap_name"] = const.pop("name").upper()
                const["unit_capacitor"] = const.pop("unit_cap").upper()
                const["size"] = const.pop("num_units")
                const["nodummy"] = not const["dummy"]
                const["cap_r"] = const["cap_s"] = -1
                del const["dummy"]
                del const["blocks"]

            elif const["const_name"] == 'Align':
                const["const_name"] = 'AlignBlock'
                if const['line'] not in ['h_bottom', 'h_top', 'h_center', 'v_right', 'v_left', 'v_center']:
                    raise NotImplementedError(f'PnR does not support edge {const["line"]} yet')

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
                const['net1'] = {"name": const['net1'], "blocks": pins1}
                const['net2'] = {"name": const['net2'], "blocks": pins2}

            elif const["const_name"] == 'PortLocation':
                for port in const["ports"]:
                    extra = {"const_name": 'PortLocation', "location": const["location"], "terminal_name": port}
                    pnr_const.append(extra)

            elif const["const_name"] == 'MultiConnection':
                for net in const["nets"]:
                    extra = {"const_name": 'Multi_Connection', "multi_number": int(const["multiplier"]), "net_name": net.upper()}
                    pnr_const.append(extra)

            elif const["const_name"] == 'NetConst':
                for net in const["nets"]:
                    if 'shield' in const and const['shield']:
                        extra = {"const_name": 'ShieldNet', "net_name": net, "shield_net": const["shield"]}
                        pnr_const.append(extra)
                    if 'criticality' in const and const['criticality']:
                        extra = {"const_name": 'CritNet', "net_name": net, "priority": const["criticality"]}
                        pnr_const.append(extra)

            elif const["const_name"] == 'NetPriority':
                for net in const["nets"]:
                    extra = {"const_name": 'CritNet', "net_name": net, "priority": const["weight"]}
                    pnr_const.append(extra)

            elif const["const_name"] == 'PlaceCloser':
                for (b1, b2) in itertools.combinations(const['blocks'], 2):
                    extra = {"const_name": 'MatchBlock', "block1": b1, "block2": b2}
                    pnr_const.append(extra)

        logger.debug(f"Constraints mapped to PnR constraints: {pnr_const}")
        return {'constraints': pnr_const}

    def _map_pins(self, pins: list):
        blocks = []
        for pin in pins:
            if '/' in pin:
                temp = {
                    "type": "pin",
                    "name": pin.split('/')[0],
                    "pin": pin.split('/')[1]
                    }
            else:
                temp = {
                    "type": "terminal",
                    "name": pin,
                    "pin": None
                    }
            blocks.append(temp)
        return blocks
