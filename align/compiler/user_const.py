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
import pydantic
from ..schema import constraint
from typing import List

logger = logging.getLogger(__name__)
pp = pprint.PrettyPrinter(indent=4)

class ConstraintParser:
    def __init__(self, pdk_dir: pathlib.Path, input_dir: pathlib.Path):
        self.input_dir = input_dir
        # pdk_dir may be needed to specialize allowed
        # constraints in future. Currently unused
        
    def read_user_const(self, design_name: str):
        """
        Reads user defined constraints and create a dictionary for each hierarchy
  
        """
        constraints = constraint.ConstraintDB()
        json_path = self.input_dir / (design_name+'.const.json')
        if json_path.is_file():
            logger.info(f"JSON input const file for block {design_name} {json_path}")
            constraints = constraint.ConstraintDB.parse_file(json_path)
        elif (self.input_dir / (design_name+'.const')).is_file():
            # TODO: Reimplement using pydantic-cli if you really want this
            raise NotImplementedError('Command-line interface has not been upgraded. Please use json constraints')
        else:
            logger.info(f"No user constraints found for block {design_name} in path {self.input_dir}")
        return constraints
            
