# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 13:18:49 2018

@author: kunal
"""
#%% creating basic element

class BasicElement:
    def __init__(self,line):
        line=line.replace(')',"").replace('(',"")
        self.line = line
        


    def Capacitor(self):
        #cap: c7 net7 vinp c1
        [capacitance, plus, minus]=self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]
        edges = [plus,minus]
        edge_weight = [1,2]
        return {"inst":capacitance, "inst_type":"cap" , "ports":edges , "edge_weight":edge_weight, "values":value}
    def Resistor(self):
        #Res: c7 net7 vinp c1
        [resistance, plus, minus]=self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]

        edges = [plus,minus]
        edge_weight = [1,2]
        return {"inst":resistance, "inst_type":"res" , "ports":edges , "edge_weight":edge_weight, "values":value}
    def Vsource(self):
        #vsource: v1 vbiasp1 0 DC=vbiasp1
        [DCsource, plus, minus, value]=self.line.strip().split()[0:4]
        edges = [plus,minus]
        edge_weight = [1,2]
        return {"inst":DCsource, "inst_type":"Vsource" , "ports":edges , "edge_weight":edge_weight, "values":value}
    def VCVSsource(self):
        #vsource: E1 (Vinp net2 net3 net2) vcvs gain=1
        #print(self.line)
        [DCsource, Iplus, Iminus, Oplus, Ominus, value]=self.line.strip().split()[0:6]
        edges = [Iplus, Iminus, Oplus, Ominus]
        edge_weight = [1,1,2,2]
        return {"inst":DCsource, "inst_type":"Vsource" , "ports":edges , "edge_weight":edge_weight, "values":value}
    def Isource(self):
        #Cur_source: i3 vdd! net1 DC=idc
        [DCsource, plus, minus, value]=self.line.strip().split()[0:4]
        edges = [plus,minus]
        edge_weight = [1,2]
        return {"inst":DCsource, "inst_type":"Isource" , "ports":edges , "edge_weight":edge_weight, "values":value}
    def Transistor(self):
        #transistor: m5 net5 phi2 0 0 nmos_rvt w=81e-9 l=20e-9 nfin=3
        #print("querying transistor",self.line)
        [inst, drain, gate, source, body, inst_type]=self.line.strip().split()[0:6]
        edges = [drain, gate, source]
        edge_weight = [1,4,2]
        value = self.line.strip().split()[6:]
        if 'n' in inst_type.lower():
            inst_type = "nmos"
        elif 'p' in inst_type.lower():
            inst_type = "pmos"    
        return {"inst":inst, "inst_type":inst_type , "ports":edges , "edge_weight":edge_weight, "values":value}
