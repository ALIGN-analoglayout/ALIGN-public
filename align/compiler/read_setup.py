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
            "POWER": [],
            "GND": [],
            "CLOCK": [],
            "DIGITAL": [],
            "DONT_USE_CELLS": [],
            "NO_CONST": [],
            "NO_ARRAY": [],
            "MERGE_SYMM_CAPS": True,
            "FIX_SD": True,
            "KEEP_DUMMY": False,
            "MERGE_SERIES": True,
            "MERGE_PARALLEL": True
            }
    if setup_path.is_file():
        logger.debug(f'Reading setup file: {setup_path}')
        fp = open(setup_path, "r")
        line = fp.readline()
        while line:
            if line.strip().upper().startswith("POWER"):
                power = line.strip().upper().split('=')[1].split()
                design_setup['POWER']=power
            elif line.strip().upper().startswith("GND"):
                GND = line.strip().upper().split('=')[1].split()
                design_setup['GND']=GND
            elif line.strip().upper().startswith("CLOCK"):
                CLOCK = line.strip().upper().split('=')[1].split()
                design_setup['CLOCK']=CLOCK
            elif line.strip().upper().startswith("DIGITAL"):
                DIGITAL = line.strip().upper().split('=')[1].split()
                design_setup['DIGITAL']=DIGITAL
            elif line.strip().upper().startswith("DONT_USE_CELLS"):
                DONT_USE_CELLS = line.strip().upper().split('=')[1].split()
                design_setup['DONT_USE_CELLS']=DONT_USE_CELLS
            elif line.strip().upper().startswith("NO_CONST"):
                NO_CONST = line.strip().upper().split('=')[1].split()
                design_setup['NO_CONST']=NO_CONST
            elif line.strip().upper().startswith("NO_ARRAY"):
                NO_CONST = line.strip().upper().split('=')[1].split()
                design_setup['NO_ARRAY'] = NO_CONST
            elif line.strip().upper().startswith("MERGE_SYMM_CAPS"):
                MERGE_SYMM_CAPS = (line.strip().upper().split('=')[1].strip() == "True")
                design_setup['MERGE_SYMM_CAPS'] = MERGE_SYMM_CAPS
            elif line.strip().upper().startswith("FIX_SOURCE_DRAIN"):
                FIX_SOURCE_DRAIN = (line.strip().upper().split('=')[1].strip() == "True")
                design_setup['FIX_SD'] = FIX_SOURCE_DRAIN
            elif line.strip().upper().startswith("KEEP_DUMMY"):
                KEEP_DUMMY = (line.strip().upper().split('=')[1].strip() == "True")
                design_setup['KEEP_DUMMY'] = KEEP_DUMMY
            elif line.strip().upper().startswith("MERGE_SERIES"):
                MERGE_SERIES = (line.strip().upper().split('=')[1].strip() == "True")
                design_setup['MERGE_SERIES'] = MERGE_SERIES
            elif line.strip().upper().startswith("MERGE_PARALLEL"):
                MERGE_PARALLEL = (line.strip().upper().split('=')[1].strip() == "True")
                design_setup['MERGE_PARALLEL'] = MERGE_PARALLEL
            else:
                logger.warning(f"Non identified values found in setup file{line}")
            line=fp.readline()
        logger.debug(f"Read SETUP: {design_setup}")
    return design_setup