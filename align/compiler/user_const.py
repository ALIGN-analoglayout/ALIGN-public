#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Wed Jan 13 14:50:24 2021

@author: kunal001
"""
import pathlib
import json
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
        combined_const_file = input_dir / 'const.json'
        self.constraint_dict = {}
        if combined_const_file.exists():
            for x in types.List[ConstJsonEntry].parse_file(combined_const_file):
                assert x.subcircuit not in self.constraint_dict
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
        json_path = [cf for cf in self.input_dir.rglob('*.const.json') if cf.stem.upper()==design_name+'.CONST']
        logger.info(f"json path {json_path} {self.input_dir}")
        if json_path and json_path[0].is_file():
            json_path = json_path[0]
            logger.debug(
                f"JSON input const file for block {design_name} {json_path}")
            with types.set_context(node):
                node.constraints.extend(
                    constraint.ConstraintDB.parse_file(json_path)
                )
            #ALL inst in caps
            for const in node.constraints:
                if hasattr(const, 'instances') and len(const.instances) > 1:
                    for i,inst in enumerate(const.instances):
                        const.instances[i] = inst.upper()
                elif hasattr(const, 'pairs'):
                    for pair in const.pairs:
                        for i,inst in enumerate(pair):
                            pair[i] = inst.upper()

            do_not_identify = []
            for const in node.constraints:
                if const.constraint == 'group_blocks':
                    continue
                if const.constraint == 'group_caps':
                    continue
                if hasattr(const, 'instances') and len(const.instances) > 1:
                    do_not_identify.extend(const.instances)
                elif hasattr(const, 'pairs'):
                    for pair in const.pairs:
                        do_not_identify.extend(pair)

            if len(do_not_identify) > 0:
                do_not_identify = list(sorted(set(do_not_identify)))
                logger.warning(f'Following instances will be excluded from subcircuit identification: {do_not_identify} ')
                with types.set_context(node.constraints):
                    node.constraints.append({'instances': do_not_identify, 'constraint':'DoNotIdentify'})

        elif (self.input_dir / (design_name+'.const')).is_file():
            # TODO: Reimplement using pydantic-cli if you really want this
            raise NotImplementedError(
                'Command-line interface has not been upgraded. Please use json constraints')
        else:
            logger.info(
                f"No user constraints found for block {design_name} in path {self.input_dir}")
