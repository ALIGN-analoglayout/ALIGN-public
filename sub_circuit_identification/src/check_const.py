# -*- coding: utf-8 -*-
"""
Created on Thu Nov 29 19:38:43 2018

@author: kunal
"""

import os
import argparse


def check_const(sub_block_const):
    """ Reads available const in input dir
        Fix cc cap in const and netlist
    """
    cc_pair={}
    const_path='input_circuit/'+sub_block_const
    if os.path.isfile(const_path): 
        print('Reading const file', const_path) 
        new_const_path=os.path.join('Results/'+sub_block_const)
        const_fp = open(const_path, "r")
        new_const_fp = open(new_const_path, "w")
        line = const_fp.readline()
        while line:
            if line.startswith("CC") and len(line.strip().split(','))>=5:
                caps_in_line = line[line.find("{")+1:line.find("}")]
                updated_cap = caps_in_line.replace(',','_')
                cap_blocks = caps_in_line.strip().split(',')
                for cap_block in cap_blocks:
                    cc_pair.update({cap_block: updated_cap})
                line = line.replace(caps_in_line,updated_cap)
            new_const_fp.write(line)
            line=const_fp.readline()
    
        const_fp.close()
        new_const_fp.close()
    else:
        print("Couldn't find constraint file",const_path," (might be okay)")

    return(cc_pair)

def fix_verilog(design_name):
    """ Reads available lef in LEF dir
    Reads .lef files or param_lef files
    """
    print("Running fix_verilog on",design_name)

    #for file in os.listdir(verilog_dir):
    #    if file.endswith(".verilog"):
    #        verilog_path = os.path.join(verilog_dir, file)
    verilog_path = './Results/'+design_name+'.v'
    if os.path.isfile(verilog_path): 

        print('Reading verilog file', verilog_path)
        new_verilog_path=os.path.join(verilog_path+'new')
        verilog_fp = open(verilog_path, "r")
        new_verilog_fp = open(new_verilog_path, "w")
        line = verilog_fp.readline()
        while line:
            if line.startswith("module"):
                match_block = {}
                new_verilog_fp.write(line)
                module_name = line.strip().split()[1]
                cc_block = check_const(module_name+'.const')
                line = verilog_fp.readline()
                if cc_block:
                    while 'endmodule' not in line:
                        try:
                            block1= line.strip().split()[1]
                            if block1 in cc_block.keys():
                                if cc_block[block1] in match_block.keys():
                                    match_block[cc_block[block1]].append(line)
                                else:
                                    match_block.update({cc_block[block1]: [line]})

                            else:
                                new_verilog_fp.write(line)
                        except:
                            new_verilog_fp.write(line)
                        line = verilog_fp.readline()
                for new_block,lines in match_block.items():
                    inst_type = "Cap"
                    inst_name = new_block
                    pins = ""
                    for idx,cc_line in enumerate(lines):
                        seg = cc_line.strip().split()
                        inst_type = inst_type + '_' + seg[0].split('_')[1]
                        pins = pins + " " + seg[3].replace('(',str(idx+1)+'(') + " " + seg[4].replace('(',str(idx+1)+'(')+"," 
                    new_b = inst_type + " " + inst_name + " ("+ pins[0:-1] + " );\n"
                    new_verilog_fp.write(new_b)
            else:
                new_verilog_fp.write(line)
                line = verilog_fp.readline()

        verilog_fp.close()
        new_verilog_fp.close()
        os.rename(new_verilog_path,verilog_path)

if __name__ == '__main__':
    PARSER = argparse.ArgumentParser(
        description="verilog_name")
    PARSER.add_argument("-f",
                        "--name",
                        type=str,
                        default='switched_capacitor_filter',
                        help='verilog module name')
    ARGS = PARSER.parse_args()
    fix_verilog(ARGS.name)
