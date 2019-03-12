# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 19:38:43 2018

@author: kunal
"""

import numpy as np
import os
def read_lef():
    dir = "./LEF/"
    lef_blocks=[]
    for file in os.listdir(dir):
        if file.endswith(".lef"):
            lef_path = os.path.join(dir, file)
            print("READING_LEF",lef_path)
            lef_fp = open(lef_path, "r")
            line = lef_fp.readline()
            while "END LIBRARY" not in line:
                if line.startswith("MACRO"): 
                    lef_blocks.append(line.strip().split()[1])
                line = lef_fp.readline()
    return lef_blocks

if __name__ == '__main__':

    available_block_lef = read_lef()
    print(available_block_lef)
