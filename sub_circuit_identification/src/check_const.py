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
            if line.startswith("CC") and len(line.strip().split(','))==5:
                updated_cc = line.strip().split(',')
                block1=updated_cc[0].strip().split('{')[-1]
                block2=updated_cc[1].strip().split('}')[0]
                cc_pair.update({block1: block2})
                updated_cc[1] = updated_cc[0].strip()+'_'+updated_cc[1].strip()
                line = line.replace(block1+','+block2,block1+'_'+block2)
            new_const_fp.write(line)
            line=const_fp.readline()
    
        const_fp.close()
        new_const_fp.close()
    #os.rename(new_const_path,const_path)
    return(cc_pair)

def fix_verilog(design_name):
    """ Reads available lef in LEF dir
    Reads .lef files or param_lef files
    """
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
                            if block1 in cc_block.keys() or  block1 in cc_block.values():
                                match_block.update({ block1: line})
                            else:
                                new_verilog_fp.write(line)
                        except:
                            new_verilog_fp.write(line)
                        line = verilog_fp.readline()
                for ele in cc_block.keys():
                    b1 = match_block[ele].strip().replace('(','1(').split()
                    b2 = match_block[cc_block[ele]].strip().replace('(','2(').split()
                    new_b = b1[0]+'_'+b2[0]+' '+ b1[1]+'_'+b2[1]+' ( '+' '.join(b1[3:-1])+', '+' '.join(b2[3:-1])+' );'
                    new_verilog_fp.write(new_b)
                    new_verilog_fp.write('\n')
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
