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
        #line = line.replace(')', "").replace('(', "")
        self.line = line
        self.pins = []

    def get_elements(self, num_pins=2):
        """ Extract pins and values"""
        self.inst =  self.line.strip().split()[0]
        if '(' in  self.line.strip().split()[1]:
            self.pins = self.line.strip().split('(')[1].split(')')[0].split()
            self.num_pins = len(self.pins)
        elif '=' in self.line.strip():
            all_words = self.line.strip().split()
            for word in all_words[1:]:
                if '=' in word:
                    self.real_inst_type = self.pins[-1]
                    del(self.pins[-1])
                    param= word.split('=')[0]
                    if not param:
                        self.real_inst_type = self.pins[-1]
                        del (self.pins[-1])
                    break
                else:
                    self.pins.append(word)
            self.num_pins = len(self.pins)
            
        else:
            self.num_pins = num_pins
            self.pins = self.line.strip().split()[1:1+self.num_pins]
            """check valid pin name"""
            if any ('=' in pin_name for pin_name in self.pins):
                self.pins=None
                self.num_pins=0
        if len(self.line.strip().split()) > self.num_pins+2:      
            self.value = self.line.strip().split()[self.num_pins+2:]
            self.real_inst_type = self.line.strip().split()[self.num_pins+1]
        else :
            self.value = self.line.strip().split()[self.num_pins+1:]
            self.real_inst_type = ""

        logging.info("real inst type from netlist: %s",self.real_inst_type)
        start = 1
        multiple = 2
        self.pin_weight = [start*multiple**i for i in range(self.num_pins)]

    def capacitor(self):
        """cap: c7 net7 vinp c1
             The assumption is 2 port network
        """
        self.get_elements(2)
        return {
            "inst": self.inst,
            "inst_type": "cap",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": self.pin_weight,
            "values": parse_value(self.value, "cap")
        }

    def resistor(self):
        """Res: c7 net7 vinp c1
             The assumption is 2 port network
        """
        self.get_elements(2)
        return {
            "inst": self.inst,
            "inst_type": "res",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": self.pin_weight,
            "values": parse_value(self.value, "res")
        }

    def inductor(self):
        """Res: c7 net7 vinp c1
             The assumption is 2 port network
        """
        self.get_elements(2)

        return {
            "inst": self.inst,
            "inst_type": "inductor",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": self.pin_weight,
            "values": parse_value(self.value, "ind")
        }

    def v_source(self):
        """v_source: v1 vbiasp1 0 DC=vbiasp1
             The assumption is 2 port network
        """
        self.get_elements(2)
        return {
            "inst": self.inst,
            "inst_type": "v_source",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": self.pin_weight,
            "values": parse_value(self.value, "DC")
        }

    def vcvs_source(self):
        """v_source: E1 (Vinp net2 net3 net2) vcvs gain=1
             The assumption is 4 port network
        """
        self.get_elements(4)
        return {
            "inst": self.inst,
            "inst_type": "v_source",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": self.pin_weight,
            "values": parse_value(self.value, "DC")
        }

    def i_source(self):
        """Cur_source: i3 vdd! net1 DC=idc
             The assumption is 2 port network
        """
        self.get_elements(2)
        return {
            "inst": self.inst,
            "inst_type": "i_source",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": self.pin_weight,
            "values": parse_value(self.value, "DC")
        }

    def transistor(self):
        """transistor: m5 net5 phi2 0 0 nmos_rvt w=81e-9 l=20e-9 nfin=3
             The assumption is 3 port network
             pins = [drain, gate, source]
        """
        #print("querying transistor",self.line)
        self.get_elements(4)
        if not self.pins:
            return None
        if 'n' in self.real_inst_type.lower():
            inst_type = "nmos"
        elif 'p' in self.real_inst_type.lower():
            inst_type = "pmos"

        if self.pins[0] == self.pins[2]:
            inst_type = "dummy"
            
        return {
            "inst": self.inst,
            "inst_type": inst_type,
            "real_inst_type": self.real_inst_type,
            "ports": self.pins[0:3],
            "edge_weight": self.pin_weight[0:3],
            "values": parse_value(self.value)
        }


def parse_value(all_param, vtype=None):
    """ parse the value parameters for each block and returns a dict"""
    device_param_list = {}
    for idx, unique_param in enumerate(all_param):
        if '=' in unique_param:
            [param, value] = unique_param.split('=')
            if not param:
                param = all_param[idx - 1]
            if not value:
                value = all_param[idx + 1]
            logging.info('Found device values: %s, value:%s', param, value)
            device_param_list[param] = value
    if not device_param_list and len(all_param)>0:
        device_param_list[vtype] =all_param[0]
    return device_param_list


def _parse_inst(line):
    """ PARSE instance lines"""
    logging.basicConfig(filename='./LOG/instances.log', level=logging.DEBUG)

    #line = line.replace("(", "").replace(")", "")
    element = BasicElement(line)
    #logging.info('READ line:'+line)
    device = None
    if not line.strip():
        return device
    elif line.strip().lower().startswith('m') \
            or line.strip().lower().startswith('n') \
            or line.strip().lower().startswith('p') \
            or line.strip().lower().startswith('xm') \
            or line.strip().lower().startswith('t'):
        logging.debug('FOUND transistor : %s', line.strip())
        device = element.transistor()
    elif line.strip().lower().startswith('v'):
        logging.debug('FOUND v_source: %s', line.strip())
        device = element.v_source()
    elif line.strip().lower().startswith('e'):
        logging.debug('FOUND vcvs_source: %s', line.strip())
        device = element.vcvs_source()
    elif line.strip().startswith('i'):
        logging.debug('FOUND i_source: %s', line.strip())
        device = element.i_source()
    elif line.strip().lower().startswith('c') or line.strip().lower().startswith('xc'):
        logging.debug('FOUND cap: %s', line.strip())
        device = element.capacitor()
    elif line.strip().lower().startswith('r') or line.strip().lower().startswith('xr'):
        logging.debug('FOUND resistor: %s', line.strip())
        device = element.resistor()
    elif line.strip().lower().startswith('l') or line.strip().lower().startswith('xl'):
        logging.debug("inductance: %s", line.strip())
        device = element.inductor()
    elif line.strip().lower().startswith('x') \
            or line.strip().startswith('I'):
        device_param_list = {}

        if ' / ' in line:
            line = line.replace(' / ', ' ')

        if line:
            all_nodes = line.strip().split()
            hier_nodes = []
            for idx, unique_param in enumerate(all_nodes):
                if '=' in unique_param:
                    [param, value] = unique_param.split('=')
                    if not param:
                        param = all_nodes[idx - 1]
                        del (hier_nodes[-1])
                    if not value:
                        value = all_nodes[idx + 1]
                        pass
                    logging.info('Found subckt parameter values: %s, value:%s',
                                 param, value)
                    device_param_list[param] = value

                else:
                    hier_nodes.append(unique_param)

        device = {
            "inst": hier_nodes[0][0:],
            "inst_type": hier_nodes[-1],
            "real_inst_type": hier_nodes[-1],
            "ports": hier_nodes[1:-1],
            "edge_weight": list(range(len(hier_nodes[1:-1]))),
            "values": device_param_list
        }
        logging.debug('FOUND subckt instance: %s, type %s ', device["inst"],
                      device["inst_type"])

    if device:
        if '=' in device["inst"] or '=' in device[
                "inst_type"] or '=' in ' '.join(device["ports"]):
            device = None
            logging.error("RECHECK unidentified Device: %s", line)
        elif  device["inst_type"]=="dummy":
            device = None
            logging.error("Removing dummy transistor: %s", line)
    else:
        logging.error("Extraction error: %s (unidentified line)", line)

    return device
