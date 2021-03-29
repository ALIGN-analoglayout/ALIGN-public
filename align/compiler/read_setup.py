#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Jan 15 16:33:11 2021

@author: kunal001
"""
import logging

logger = logging.getLogger(__name__)

def read_setup(setup_path):
    design_setup = {
            "POWER":['vdd'],
            "GND":[],
            "CLOCK":[],
            "DIGITAL":[],
            "DONT_USE_CELLS":[],
            "NO_CONST":[],
            "NO_ARRAY": [],
            "MERGE_SYMM_CAPS":True
            }
    if setup_path.is_file():
        logger.debug(f'Reading setup file: {setup_path}')
        fp = open(setup_path, "r")
        line = fp.readline()
        while line:
            if line.strip().startswith("POWER"):
                power = line.strip().split('=')[1].split()
                design_setup['POWER']=power
            elif line.strip().startswith("GND"):
                GND = line.strip().split('=')[1].split()
                design_setup['GND']=GND
            elif line.strip().startswith("CLOCK"):
                CLOCK = line.strip().split('=')[1].split()
                design_setup['CLOCK']=CLOCK
            elif line.strip().startswith("DIGITAL"):
                DIGITAL = line.strip().split('=')[1].split()
                design_setup['DIGITAL']=DIGITAL
            elif line.strip().startswith("DONT_USE_CELLS"):
                DONT_USE_CELLS = line.strip().split('=')[1].split()
                design_setup['DONT_USE_CELLS']=DONT_USE_CELLS
            elif line.strip().startswith("NO_CONST"):
                NO_CONST = line.strip().split('=')[1].split()
                design_setup['NO_CONST']=NO_CONST
            elif line.strip().startswith("NO_ARRAY"):
                NO_CONST = line.strip().split('=')[1].split()
                design_setup['NO_ARRAY'] = NO_CONST
            elif line.strip().startswith("MERGE_SYMM_CAPS"):
                MERGE_SYMM_CAPS = (line.strip().split('=')[1].strip() == "True")
                design_setup['MERGE_SYMM_CAPS'] = MERGE_SYMM_CAPS
            else:
                logger.warning(f"Non identified values found in setup file{line}")
            line=fp.readline()
        logger.debug(f"SETUP: {design_setup}")
    else:
        logger.warning(f"no setup file found: {setup_path}")
    return design_setup