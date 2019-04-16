# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 19:38:43 2018

@author: kunal
"""

import os


def read_lef():
    """ Reads available lef in LEF dir
    Reads .lef files or param_lef files
    """
    lef_dir = "./LEF/"
    lef_blocks = []
    for file in os.listdir(lef_dir):
        if file.endswith(".lef"):
            lef_path = os.path.join(lef_dir, file)
            print("READING_LEF", lef_path)
            lef_fp = open(lef_path, "r")
            line = lef_fp.readline()
            while "END LIBRARY" not in line:
                if line.startswith("MACRO"):
                    lef_blocks.append(line.strip().split()[1])
                line = lef_fp.readline()
        elif file.endswith("param_lef"):
            param_lef_path = os.path.join(lef_dir, file)
            with open(param_lef_path) as param_lef_file:
                lines = param_lef_file.read().splitlines()
                lef_blocks.extend(lines)
    return lef_blocks


if __name__ == '__main__':

    AVAILABLE_BLOCK_LEF = read_lef()
    print(AVAILABLE_BLOCK_LEF)
