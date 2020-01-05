#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Tue Oct 22 21:06:36 2019

@author: kunal001
"""

import os
import logging

if not os.path.exists("./LOG"):
    os.mkdir("./LOG")
elif os.path.exists("./LOG/read_netlist.log"):
    os.rename("./LOG/read_netlist.log", "./LOG/read_netlist.log1")
    
logging.basicConfig(filename='./LOG/read_netlist.log', level=logging.DEBUG)

OTA_DIR = "OTA"
BIAS_DIR = "BIAS"
LG_DIR = "Local_generation"

OTA_NETLIST = os.listdir(OTA_DIR)
LG_NETLIST = os.listdir(LG_DIR)
BIAS_NETLIST = os.listdir(BIAS_DIR)


class create_OTA_connection:
    
    def __init__(self,line):
        self.line =line
        self.bias_ports =[]
        self.LG_connect_pins =[]
        self.insts = []
        self.LG_input = None
        self.ota_inst()
    def ota_inst(self):
        words=line.split()
        for idx, port in enumerate(words):
            if 'bias' in port:
                words[idx]="LG_"+port
                self.bias_ports.append("LG_"+port)
        self.insts.append(  "\nxiota "+ " ".join(words[2:]) + \
                                " "+ words[1])
    def LG_pins(self,lg_pins,lg_type):
        
        if "LG_Vbiasn2" in  self.bias_ports:
            if "Vbiasn2" not in lg_pins:
                logging.error("Vbiasn2 not in lg_pins:%s,%s",self.insts[0],lg_type)
                return 0
        elif "LG_Vbiasp2" in  self.bias_ports:
            if "Vbiasp2" not in lg_pins:
                logging.error("Vbiasp2 not in lg_pins:%s,%s",self.insts[0],lg_type)
                return 0
        elif "LG_Vbiasn2" not in  self.bias_ports:
            if "Vbiasn2" in lg_pins:
                logging.error("Vbiasn2 in lg_pins:%s,%s",self.insts[0],lg_type)
                return 0
        elif "LG_Vbiasp2" not in  self.bias_ports:
            if "Vbiasp2" in lg_pins:
                logging.error("Vbiasp2 in lg_pins:%s,%s",self.insts[0],lg_type)
                return 0
        if "LG_Vbiasn1" not in  self.bias_ports:
            if "Vbiasn1" in lg_pins:
                logging.error("Vbiasn1 in lg_pins:%s,%s",self.insts[0],lg_type)
                return 0 
        elif "LG_Vbiasp1" not in  self.bias_ports:
            if "Vbiasp1" in lg_pins:
                logging.error("Vbiasp1 in lg_pins:%s,%s",self.insts[0],lg_type)
                return 0 
        words=lg_pins.split()[1:]
        added = 0         
        for idx, port in enumerate(words):
            if 'bias' in port and port.endswith('O'):
                check_port = "LG_"+port.replace(':O','')
                words[idx] = check_port
                if check_port in self.bias_ports:
                    self.LG_connect_pins.append(check_port)
                    added = 1
            elif port.endswith(':I') and 'ias' in port:
                self.LG_input = port.replace(':I','') 
                words[idx]= self.LG_input
            else:
                words[idx] = port.replace(':I','').replace(':O','')
           
        if added ==1: 
            self.insts.append("\nxi"+lg_type+" " +" ".join(words) +" "+lg_type)
            return 1
        else:
            return 0
        
    def BIAS_pins(self,bias_line):
        words=bias_line.split()
        for idx, port in enumerate(words):
            port = port.replace("Vbias","Bias")
            words[idx] = port
            if self.LG_input ==port:
                self.insts.append("\nxib"+words[1]+" "+ \
                                  " ".join(words[2:])+ " "+words[1])
                return 1

        return 0

def read_LG_bias(file, connect):
    BIAS_lines=[]
    found=0
    if 'LG' in file:
        FLAG =0
        with open(file, "r") as file:
            name =""
            for line in file:
                if ".SUBCKT" in line: 
                    name = line.split()[1]
                    FLAG=1
                elif ".PININFO" in line:
                    found = connect.LG_pins(line,name)
                elif ".ENDS" in line:
                    FLAG=0
                    BIAS_lines.append(line)
                if FLAG==1:
                    BIAS_lines.append(line)
    if found:
        return BIAS_lines
    else:
        return None          
    
def read_bias(file, connect):
    BIAS_lines=[]
    found=0
    if file.endswith('.sp'):
        FLAG =0
        with open(file, "r") as file:
            for line in file:
                if ".SUBCKT" in line: 
                    found=connect.BIAS_pins(line)
                    FLAG=1
                elif ".ENDS" in line:
                    FLAG=0
                    BIAS_lines.append(line)
                if FLAG==1:
                    BIAS_lines.append(line)
    if found:
        return BIAS_lines
    else:
        return None   
              
for ON in OTA_NETLIST:
    if "_" in ON:
        with open(OTA_DIR+"/"+ON, "r") as file:
            OTA_lines = []
            for line in file:
                if ".SUBCKT" in line: 
                    connect = create_OTA_connection(line)
                OTA_lines.append(line)

        for LN in LG_NETLIST:
            for BN in BIAS_NETLIST:
                LG_lines =[]
                BG_lines =[]
                connect.insts=[connect.insts[0]]
                check_lg = read_LG_bias(LG_DIR+"/"+LN, connect)
                if check_lg:
                    check_bias = read_bias(BIAS_DIR+"/"+BN, connect)
                    if check_bias:
                        print("Creating combination of: " +ON + ", " +LN + ", "+ BN)
                        fo= open("FULL_OTA/"+ON+"_"+LN+"_"+BN,"w")
                        LG_lines = LG_lines+check_lg
                        BG_lines = BG_lines + check_bias
                        for line in OTA_lines:
                            fo.write(line)
                        fo.write("\n")
                        for line in LG_lines:
                            fo.write(line)
                        fo.write("\n")
                        for line in BG_lines:
                            fo.write(line)
                        fo.write("\n")
                            
                        for connect_line in connect.insts:
                            fo.write(connect_line)
                
                        fo.write("\n.END")
                        fo.close
            
        
        
