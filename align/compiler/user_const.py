#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Jan 13 14:50:24 2021

@author: kunal001
"""
import pathlib
import logging
from ..schema import constraint, types

logger = logging.getLogger(__name__)


class ConstJsonEntry(types.BaseModel):
    subcircuit: str
    constraints: types.List[types.Dict]


class ConstraintParser:
    def __init__(self, pdk_dir: pathlib.Path, input_dir: pathlib.Path):
        self.input_dir = input_dir
        # pdk_dir may be needed to specialize allowed
        # constraints in future. Currently unused

        # Handle combined const.json file here
        combined_const_file = input_dir / "const.json"
        self.constraint_dict = {}
        if combined_const_file.exists():
            for x in types.List[ConstJsonEntry].parse_file(combined_const_file):
                assert x.subcircuit not in self.constraint_dict, f"already existing constraint in {self.constraint_dict} for {x.subcircuit}"
                self.constraint_dict[x.subcircuit] = x.constraints

    def annotate_user_constraints(self, node):
        """
        Annotates user defined constraints into HierDictNode.constraints
        """
        design_name = node.name
        if design_name in self.constraint_dict:
            with types.set_context(node.constraints):
                for const in self.constraint_dict[design_name]:
                    node.constraints.append(const)
        json_path = [
            cf
            for cf in self.input_dir.rglob("*.const.json")
            if cf.stem.upper() == design_name + ".CONST"
        ]
        if json_path and json_path[0].is_file():
            logger.info(f"Reading constraint file: {json_path}")
            json_path = json_path[0]
            logger.debug(f"JSON input const file for block {design_name} {json_path}")
            with types.set_context(node):
                constraints = constraint.ConstraintDB.parse_file(json_path)
            with types.set_context(node.constraints):
                node.constraints.extend(constraints)
            # ALL inst in caps
            for const in node.constraints:
                if hasattr(const, "instances") and len(const.instances) > 0:
                    for i, inst in enumerate(const.instances):
                        const.instances[i] = inst.upper()
                elif hasattr(const, "pairs"):
                    for pair in const.pairs:
                        for i, inst in enumerate(pair):
                            pair[i] = inst.upper()

            do_not_identify = []
            for const in node.constraints:
                if isinstance(const, constraint.GroupBlocks) or \
                    isinstance(const, constraint.GroupCaps):
                    continue
                if hasattr(const, "instances") and len(const.instances) > 1:
                    do_not_identify.extend(const.instances)
                elif hasattr(const, "pairs"):
                    for pair in const.pairs:
                        do_not_identify.extend(pair)
                elif hasattr(const, "pins1") and const.pins1:
                    _pin_inst = [pin.split('/')[0] for pin in const.pins1+const.pins2 if '/' in pin]
                    do_not_identify.extend(_pin_inst)


            if len(do_not_identify) > 0:
                do_not_identify = list(sorted(set(do_not_identify)))
                logger.debug(f"Following instances will be excluded from subcircuit identification: {do_not_identify}")
                with types.set_context(node.constraints):
                    node.constraints.append(
                        {"instances": do_not_identify, "constraint": "DoNotIdentify"}
                    )
        else:
            logger.debug(f"No user constraints found for block {design_name} in path {self.input_dir}")
