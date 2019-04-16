# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 13:18:49 2018

@author: kunal
"""
#%% creating basic element
import logging

class BasicElement:
    """
    Defines the basic elements of spice file
    e.g: a resistor, inductor
    It also defines the weight on each port of device
    """
    def __init__(self, line):
        line = line.replace(')', "").replace('(', "")
        self.line = line

    def capacitor(self):
        """cap: c7 net7 vinp c1"""
        [capacitance, plus, minus] = self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]
        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": capacitance,
            "inst_type": "cap",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }

    def resistor(self):
        """Res: c7 net7 vinp c1"""
        [resistance, plus, minus] = self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]

        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": resistance,
            "inst_type": "res",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }

    def inductor(self):
        """Res: c7 net7 vinp c1"""
        [inductance, plus, minus] = self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]

        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": inductance,
            "inst_type": "ind",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }
    def v_source(self):
        """v_source: v1 vbiasp1 0 DC=vbiasp1"""
        [dc_source, plus, minus, value] = self.line.strip().split()[0:4]
        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": dc_source,
            "inst_type": "v_source",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }

    def vcvs_source(self):
        """v_source: E1 (Vinp net2 net3 net2) vcvs gain=1"""
        [dc_source, in_plus, in_minus, out_plus, out_minus,
         value] = self.line.strip().split()[0:6]
        edges = [in_plus, in_minus, out_plus, out_minus]
        edge_weight = [1, 1, 2, 2]
        return {
            "inst": dc_source,
            "inst_type": "v_source",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }

    def i_source(self):
        """Cur_source: i3 vdd! net1 DC=idc"""
        [dc_source, plus, minus, value] = self.line.strip().split()[0:4]
        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": dc_source,
            "inst_type": "i_source",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }

    def transistor(self):
        """transistor: m5 net5 phi2 0 0 nmos_rvt w=81e-9 l=20e-9 nfin=3"""
        #print("querying transistor",self.line)
        [inst, drain, gate, source, body,
         inst_type] = self.line.strip().split()[0:6]
        edges = [drain, gate, source]
        edge_weight = [1, 4, 2]
        value = self.line.strip().split()[6:]
        if 'n' in inst_type.lower():
            inst_type = "nmos"
        elif 'p' in inst_type.lower():
            inst_type = "pmos"
        return {
            "inst": inst,
            "inst_type": inst_type,
            "ports": edges,
            "edge_weight": edge_weight,
            "values": value
        }

def _parse_inst(line):
    """ PARSE instance lines"""
    logging.basicConfig(filename='./LOG/instances.log', level=logging.DEBUG)

    line = line.replace("(", "").replace(")", "")
    element = BasicElement(line)
    #logging.info('READ line:'+line)
    device = None
    if not line.strip():
        return device
    elif line.strip().lower().startswith('m') \
            or line.strip().lower().startswith('n') \
            or line.strip().lower().startswith('p') \
            or line.strip().lower().startswith('t'):
        logging.info('FOUND transistor')
        device = element.transistor()
    elif line.strip().lower().startswith('v'):
        logging.info('FOUND v_source')
        device = element.v_source()
    elif line.strip().lower().startswith('e'):
        logging.info('FOUND vcvs_source')
        logging.debug("v_source: %s", line)
        device = element.vcvs_source()
    elif line.strip().startswith('i'):
        logging.info('FOUND i_source')
        device = element.i_source()
    elif line.strip().lower().startswith('c'):
        logging.info('FOUND cap')
        device = element.capacitor()
    elif line.strip().lower().startswith('r'):
        logging.info('FOUND resistor')
        logging.debug("resistance: %s", line)
        device = element.resistor()
    elif line.strip().lower().startswith('l'):
        logging.info('FOUND inductor')
        logging.debug("inductance: %s", line)
        device = element.inductor()
    elif line.strip().lower().startswith('x') \
            or line.strip().startswith('I'):
        if ' / ' in line:
            line = line.replace(' / ', ' ')
        elif '(' in line:
            line = line.replace('(', ' ').replace(')', ' ')

        hier_nodes = line.strip().split()
        device = {
            "inst": hier_nodes[0][0:],
            "inst_type": hier_nodes[-1],
            "ports": hier_nodes[1:-1],
            "edge_weight": list(range(len(hier_nodes[1:-1]))),
            "values": None
        }
        logging.info('FOUND subckt instance: %s', device["inst_type"])
    else:
        logging.info("FOUND  unidentified Device: %s", line)
        return device
    return device
