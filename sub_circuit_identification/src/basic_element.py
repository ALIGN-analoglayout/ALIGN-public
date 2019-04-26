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
        """cap: c7 net7 vinp c1
             The assumption is 2 port network
        """
        [capacitance, plus, minus] = self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]
        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": capacitance,
            "inst_type": "cap",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": parse_value(value)
        }

    def resistor(self):
        """Res: c7 net7 vinp c1
             The assumption is 2 port network
        """
        [resistance, plus, minus] = self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]

        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": resistance,
            "inst_type": "res",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": parse_value(value)
        }

    def inductor(self):
        """Res: c7 net7 vinp c1
             The assumption is 2 port network
        """
        [inductance, plus, minus] = self.line.strip().split()[0:3]
        value = self.line.strip().split()[3:]

        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": inductance,
            "inst_type": "ind",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": parse_value(value)
        }

    def v_source(self):
        """v_source: v1 vbiasp1 0 DC=vbiasp1
             The assumption is 2 port network
        """
        [dc_source, plus, minus, value] = self.line.strip().split()[0:4]
        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": dc_source,
            "inst_type": "v_source",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": parse_value(value)
        }

    def vcvs_source(self):
        """v_source: E1 (Vinp net2 net3 net2) vcvs gain=1
             The assumption is 2 port network
        """
        [dc_source, in_plus, in_minus, out_plus, out_minus,
         value] = self.line.strip().split()[0:6]
        edges = [in_plus, in_minus, out_plus, out_minus]
        edge_weight = [1, 1, 2, 2]
        return {
            "inst": dc_source,
            "inst_type": "v_source",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": parse_value(value)
        }

    def i_source(self):
        """Cur_source: i3 vdd! net1 DC=idc
             The assumption is 2 port network
        """
        [dc_source, plus, minus, value] = self.line.strip().split()[0:4]
        edges = [plus, minus]
        edge_weight = [1, 2]
        return {
            "inst": dc_source,
            "inst_type": "i_source",
            "ports": edges,
            "edge_weight": edge_weight,
            "values": parse_value(value)
        }

    def transistor(self):
        """transistor: m5 net5 phi2 0 0 nmos_rvt w=81e-9 l=20e-9 nfin=3
             The assumption is 2 port network
        """
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
            "values": parse_value(value)
        }


def parse_value(all_param):
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
    return device_param_list


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
    elif line.strip().lower().startswith('c'):
        logging.debug('FOUND cap: %s', line.strip())
        device = element.capacitor()
    elif line.strip().lower().startswith('r'):
        logging.debug('FOUND resistor: %s', line.strip())
        device = element.resistor()
    elif line.strip().lower().startswith('l'):
        logging.debug("inductance: %s", line.strip())
        device = element.inductor()
    elif line.strip().lower().startswith('x') \
            or line.strip().startswith('I'):
        device_param_list = {}

        if ' / ' in line:
            line = line.replace(' / ', ' ')
        elif '(' in line:
            line = line.replace('(', ' ').replace(')', ' ')
        else:
            all_nodes = line.strip().split()
            hier_nodes = []
            for idx, unique_param in enumerate(all_nodes):
                if '=' in unique_param:
                    [param, value] = unique_param.split('=')
                    if not param:
                        param = all_param[idx - 1]
                        del (hier_nodes[-1])
                    if not value:
                        value = all_param[idx + 1]
                        pass
                    logging.info('Found subckt parameter values: %s, value:%s',
                                 param, value)
                    device_param_list[param] = value

                else:
                    hier_nodes.append(unique_param)

        device = {
            "inst": hier_nodes[0][0:],
            "inst_type": hier_nodes[-1],
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
    else:
        logging.error("Extraction error: %s (unidentified line)", line)

    return device
