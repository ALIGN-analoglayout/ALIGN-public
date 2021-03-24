# -*- coding: utf-8 -*-
"""
Created on Wed Oct 10 13:18:49 2018

@author: kunal
"""

import logging
logger = logging.getLogger(__name__)

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
        ## UW circuits have - sign which is not handled by placer now"
        self.inst =  self.line.strip().split()[0].replace('-','_')
        if '(' in  self.line.strip().split()[1]:
            self.pins = self.line.strip().split('(')[1].split(')')[0].split()
            self.num_pins = len(self.pins)
            self.line = self.line.replace('(','').replace(')','')
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
        if self.pins and '0' in self.pins:
            for n, i in enumerate(self.pins):
                if i=='0':
                    self.pins[n]='vss'


        logger.debug(f"real inst type from netlist: {self.real_inst_type}")
        start = 1
        multiple = 2
        self.pin_weight = [start*multiple**i for i in range(self.num_pins)]

    def capacitor(self):
        """cap: c7 net7 vinp c1
             The assumption is 2 port network
        """
        self.get_elements(2)
        value = parse_value(self.value, "cap")
        if 'c' in value.keys():
            value['cap'] = value['c']
            del value['c']
        return {
            "inst": self.inst,
            "inst_type": "cap",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": [1]*(self.num_pins),
            "values": value
        }

    def resistor(self):
        """Res: c7 net7 vinp c1
             The assumption is 2 port network
        """
        self.get_elements(2)
        value = parse_value(self.value, "res")
        if 'r' in value.keys():
            value['res'] = value['r']
            del value['r']
        return {
            "inst": self.inst,
            "inst_type": "res",
            "real_inst_type": self.real_inst_type,
            "ports": self.pins,
            "edge_weight": [1]*(self.num_pins),
            "values": value
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
            "edge_weight": [1]*(self.num_pins),
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
             The assumption is 4 port network
             pins = [drain, gate, source, body]
        """
        logger.debug(f"Querying transistor {self.line}")
        self.get_elements(4)
        if not self.pins:
            return None
        if 'n' in self.real_inst_type.lower():
            inst_type = "nmos"
        elif 'p' in self.real_inst_type.lower():
            inst_type = "pmos"
        else:
            logger.error(f"Undefined inst format {self.line}")

        #if self.pins[0] == self.pins[2]:
        #    inst_type = "dummy"
        #self.pin_weight[0] = self.pin_weight[2]
        return {
            "inst": self.inst,
            "inst_type": inst_type,
            "real_inst_type": self.real_inst_type,
            "ports": self.pins[0:4],
            "edge_weight": self.pin_weight[0:4],
            "values": parse_value(self.value)
        }


def parse_value(all_param, vtype=None):
    """ parse the value parameters for each block and returns a dict"""
    device_param_list = {}
    for idx, unique_param in enumerate(all_param):
        if '=' in unique_param:
            #making all values to lower case
            [param, value] = unique_param.lower().split('=')
            if not param:
                param = all_param[idx - 1]
            if not value:
                value = all_param[idx + 1]
            logger.debug(f'Found device values: {param}, value: {value}')
            device_param_list[param] = value
    if not device_param_list and len(all_param)>0:
        device_param_list[vtype] =all_param[0]
    return device_param_list


def _parse_inst(line):
    """ PARSE instance lines"""

    #line = line.replace("(", "").replace(")", "")
    element = BasicElement(line)
    #logger.debug('READ line:'+line)
    device = None
    if not line.strip():
        return device
    elif line.strip().lower().startswith('m'):
        logger.debug(f'FOUND transistor : {line.strip()}')
        device = element.transistor()
    elif line.strip().lower().startswith('v'):
        logger.debug(f'FOUND v_source: {line.strip()}')
        device = element.v_source()
    elif line.strip().lower().startswith('e'):
        logger.debug(f'FOUND vcvs_source: {line.strip()}')
        device = element.vcvs_source()
    elif line.strip().startswith('i'):
        logger.debug(f'FOUND i_source: {line.strip()}')
        device = element.i_source()
    elif line.strip().lower().startswith('c') \
            or (line.strip().lower().startswith('xc') \
            and 'cap' in  line.strip().split()[3].lower()):
        #DESIGN=Sanitized_TX_8l12b has XC for caps
        logger.debug(f'FOUND cap: {line.strip()}')
        device = element.capacitor()
    elif line.strip().lower().startswith('r') \
            or (line.strip().lower().startswith('xr') \
            and 'res' in line.strip().split()[3].lower()):
        #modified for frontend design from NW
        logger.debug(f'FOUND resistor: {line.strip()}')
        device = element.resistor()
    elif line.strip().lower().startswith('l'):
        logger.debug(f"inductance: {line.strip()}")
        device = element.inductor()
    elif line.strip().lower().startswith('x') \
            or line.strip().startswith('I'):
        #split the line into four fileds instance name,ports,instance type,parameters
        device_param_list = {}

        if ' / ' in line:
            line = line.replace(' / ', ' ')
        if '(' in line:
            line = line.replace('(', '').replace(')', '')

        if line:
            fields = line.strip().split()
            hier_nodes = []
            for idx, field in enumerate(fields):
                if '=' in field:
                    [param, value] = field.split('=')
                    if not param:
                        param = fields[idx - 1]
                        del (hier_nodes[-1])
                    if not value:
                        value = fields[idx + 1]
                        pass
                    logger.debug(f'Found subckt parameter values: {param}, value: {value}')
                    device_param_list[param] = value

                else:
                    hier_nodes.append(field)

        device = {
            "inst": hier_nodes[0][0:],
            "inst_type": hier_nodes[-1],
            "real_inst_type": hier_nodes[-1],
            "ports": hier_nodes[1:-1],
            "values": device_param_list
        }
        logger.debug(f'FOUND subckt instance: {device["inst"]}, type {device["inst_type"]}')

    if device:
        if '=' in device["inst"] or '=' in device[
                "inst_type"] or '=' in ' '.join(device["ports"]):
            device = None
            logger.error(f"RECHECK unidentified Device: {line}")
        elif  device["inst_type"]=="dummy":
            #device = None
            logger.error(f"Removing dummy transistor: {line}")
        #added to avoid assertion for string in PnR
        if device["inst_type"][0].isdigit():
            device["inst_type"] = "align_"+device["inst_type"]

    elif line.startswith('*'):
        logger.debug(f"comment: {line}")
    else:
        logger.warning(f"Extraction error: {line} (unidentified line)")

    return device
