# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 19:38:43 2018

@author: kunal
"""

import logging
import os

logger = logging.getLogger(__name__)


def read_lef(lef_dir):
    """ Reads available lef in LEF dir
    Reads .lef files or param_lef files
    """
    lef_blocks = []
    for file in os.listdir(lef_dir):
        if file.endswith(".lef"):
            lef_path = os.path.join(lef_dir, file)
            logger.debug(f"READING_LEF {lef_path}")
            with open(lef_path, "r") as lef_fp:
                line = lef_fp.readline()
                while line:
                    if line.startswith("MACRO"):
                        lef_blocks.append(line.strip().split()[1])
                    line = lef_fp.readline()
        elif file.endswith("param_lef"):
            param_lef_path = os.path.join(lef_dir, file)
            with open(param_lef_path) as param_lef_fp:
                lines = param_lef_fp.read().splitlines()
                lef_blocks.extend(lines)
    return lef_blocks
