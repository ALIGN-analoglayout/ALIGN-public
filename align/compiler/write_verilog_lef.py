# -*- coding: utf-8 -*-
"""
Created on Wed Nov 21 13:12:15 2018

@author: kunal
"""
from math import sqrt, ceil,floor

from .util import convert_to_unit

import logging
logger = logging.getLogger(__name__)


class WriteVerilog:
    """ write hierarchical verilog file """

    def __init__(self, circuit_graph, circuit_name, inout_pin_names,subckt_dict, power_pins, constraints):
        self.circuit_graph = circuit_graph
        self.circuit_name = circuit_name
        self.inout_pins = inout_pin_names
        self.pins = []
        for port in sorted(inout_pin_names):
            if port not in power_pins:
                self.pins.append(port)
        self.power_pins=power_pins
        self.subckt_dict = subckt_dict
        self.constraints = constraints

    def gen_dict( self):
        d = {}
        d['name'] = self.circuit_name
        d['parameters'] = self.pins
        d['constraints'] = self.constraints.dict()['__root__']
        d['instances'] = []

        for node, attr in self.circuit_graph.nodes(data=True):


            if 'source' in attr['inst_type']:
                logger.debug(f"Skipping source nodes : {node}")
                continue
            if 'net' not in attr['inst_type']:
                logger.debug(f"Writing node: {node} {attr}")

                instance = {}

                instance['template_name'] = attr['inst_type']
                instance['instance_name'] = node

                ports = []
                nets = []
                if "ports_match" in attr:
                    logger.debug(f'Nets connected to ports: {attr["ports_match"]}')
                    for key, value in attr["ports_match"].items():
                        ports.append(key)
                        nets.append(value)
                    if 'Switch_NMOS_G' in attr['inst_type']:
                        ports.append('B')
                        nets.append(nets[1])
                    elif 'Switch_PMOS_G' in attr['inst_type']:
                        ports.append('B')
                        nets.append(nets[1])
                elif "connection" in attr and attr["connection"]:
                    for key, value in attr["connection"].items():
                        if attr['inst_type'] in self.subckt_dict and key in self.subckt_dict[attr['inst_type']]['ports']:
                            ports.append(key)
                            nets.append(value)
                else:
                    logger.error(f"No connectivity info found : {', '.join(attr['ports'])}")
                    ports = attr["ports"]
                    nets = list(self.circuit_graph.neighbors(node))

                print(instance)
                print(ports)
                print(nets)
                instance['fa_map'] = self.gen_dict_fa(ports, nets)
                if not instance['fa_map']:
                    logger.warning(f"Unconnected module, only power/gnd conenction found {node}")

                d['instances'].append( instance)

        return d

    def gen_dict_fa(self, a, b):
        if len(a) == len(b):
            mapped_pins = []
            for ai, bi in zip(a, b):
                if ai not in self.power_pins:
                    mapped_pins.append( { "formal" : ai, "actual" : bi})
            return list(sorted(mapped_pins,key=lambda x:x['formal']))
        elif len(set(a)) == len(set(b)):
            if len(a) > len(b):
                mapped_pins = []
                check_short = []
                no_of_short = 0
                for i in range(len(a)):
                    if a[i] in check_short:
                        mapped_pins.append(mapped_pins[check_short.index(a[i])])
                        no_of_short += 1
                    else:
                        mapped_pins.append( { "formal" : a[i], "actual": b[i - no_of_short]})
                        check_short.append(a[i])
                    if a[i] in self.power_pins:
                        mapped_pins= mapped_pins[:-1]

                return list(sorted(mapped_pins,key=lambda x:x['formal']))

        else:
            logger.error( f"unmatched ports found: {a} {b}")
            assert False

def write_verilog( j, ofp):

    for module in j['modules']:
        print( f"module {module['name']} ( {', '.join( module['parameters'])} );", file=ofp) 
        print( f"input {', '.join( module['parameters'])};", file=ofp) 
        print( file=ofp)
        for instance in module['instances']:
            pl = ', '.join( f".{fa['formal']}({fa['actual']})" for fa in instance['fa_map'])
            print( f"{instance['template_name']} {instance['instance_name']} ( {pl} );", file=ofp)

        print( file=ofp)
        print( 'endmodule', file=ofp)
        
    if 'global_signals' in j and j['global_signals']:
        prefixes = set()
        for s in j['global_signals']:
            prefixes.add( s['prefix'])
        assert 1 == len(prefixes)
        prefix = list(prefixes)[0]
        print( file=ofp)
        print( "`celldefine", file=ofp)
        print( f"module {prefix};", file=ofp)
        for s in j['global_signals']:
            formal, actual = s['formal'], s['actual']
            print( f'{formal} {actual};', file=ofp)
        print( "endmodule", file=ofp)
        print( "`endcelldefine", file=ofp)


def generate_lef(name:str, attr:dict, available_block_lef:list, design_config:dict, uniform_height=False):
    """ Return commands to generate parameterized lef"""
    values=attr["values"]
    logger.debug(f"checking lef for: {name}, {values}")
    #for param, value in size.items():

    if name.lower().startswith('cap'):
        #print("all val",values)
        if 'cap' in values.keys():
            if values["cap"]=="unit_size":
                size = design_config["unit_size_cap"]
            else:
                size = float('%g' % (round(values["cap"] * 1E15,4)))
            num_of_unit = float(size)/design_config["unit_size_cap"]
            block_name = name + '_' + str(int(size)) + 'f'
        else:
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
            size = size.replace('.','p').replace('-','_neg_')
            num_of_unit=1
            block_name = name + '_' + str(size)

        logger.debug(f"Found cap with size: {size}, {design_config['unit_size_cap']}")
        unit_block_name = 'Cap_' + str(design_config["unit_size_cap"]) + 'f'
        if block_name in available_block_lef:
            return block_name, available_block_lef[block_name]
        logger.debug(f'Generating lef for: {name}, {size}')
        if  num_of_unit > 128:
            return block_name, {
                'primitive': block_name,
                'value': int(size)
            }
        else:
            return unit_block_name, {
                'primitive': block_name,
                'value': design_config["unit_size_cap"]
            }
    elif name.lower().startswith('res'):
        if 'res' in values.keys():
            if values["res"]=="unit_size":
                size = design_config["unit_height_res"]
            else:
                size = '%g'%(round(values["res"],2))
        else :
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        block_name = name + '_' + str(size).replace('.','p')
        try:
            height = ceil(sqrt(float(size) / design_config["unit_height_res"]))
            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            logger.debug(f'Generating lef for: {block_name} {size}')
            return block_name, {
                'primitive': name,
                'value': (height, float(size))
            }
        except:
            return block_name, {
                'primitive': name,
                'value': (1, design_config["unit_height_res"])
            }
    else:
        if 'nmos' in name.lower():
            unit_size_mos = design_config["unit_size_nmos"]
        else:
            unit_size_mos = design_config["unit_size_pmos"]
        if "nfin" in values.keys():
            #FinFET design
            if values["nfin"]=="unit_size":
                size = unit_size_mos
            else:
                size = int(values["nfin"])
            name_arg ='nfin'+str(size)
        elif "w" in values.keys():
            #Bulk design
            if values["w"]=="unit_size":
                size = unit_size_mos
            else:
                size = int(values["w"]*1E+9/design_config["Gate_pitch"])                
            values["nfin"]=size
            name_arg ='nfin'+str(size)
        else:
            convert_to_unit(values)
            size = '_'.join(param+str(values[param]) for param in values)
        if 'nf' in values.keys():
            if values['nf'] == 'unit_size':
                values['nf'] =size
            size=size*int(values["nf"])
            name_arg =name_arg+'_nf'+str(int(values["nf"]))

        if 'm' in values.keys():
            if values['m'] == 'unit_size':
                values['m'] = 1
            size=size*int(values["m"])
            name_arg =name_arg+'_m'+str(int(values["m"]))

        no_units = ceil(size / unit_size_mos)

        logger.debug('Generating lef for: %s %s', name, str(size))
        if isinstance(size, int):
            no_units = ceil(size / unit_size_mos)
            if any(x in name for x in ['DP','_S']) and floor(sqrt(no_units/3))>=1:
                square_y = floor(sqrt(no_units/3))
            else:
                square_y = floor(sqrt(no_units))
            while no_units % square_y != 0:
                square_y -= 1
            yval = square_y
            xval = int(no_units / square_y)
            block_name = f"{name}_{name_arg}_n{unit_size_mos}_X{xval}_Y{yval}"

            if block_name in available_block_lef:
                return block_name, available_block_lef[block_name]
            if name == 'Switch_NMOS_G':
                #TBD in celll generator
                name = 'Switch_NMOS_B'
            elif name == 'Switch_PMOS_G':
                name = 'Switch_PMOS_B'

            logger.debug(f"Generating parametric lef of:  {block_name} {name}")
            values["real_inst_type"]=attr["real_inst_type"]
            cell_gen_parameters= {
                'primitive': name,
                'value': unit_size_mos,
                'x_cells': xval,
                'y_cells': yval,
                'parameters':values
            }
            if 'stack' in values.keys():
                cell_gen_parameters['stack']=int(values["stack"])
                block_name = block_name+'_ST'+str(int(values["stack"]))
            #cell generator takes only one VT so doing a string search
            #To be fixed:
            if isinstance(attr["real_inst_type"],list):
                merged_vt='_'.join(attr["real_inst_type"])
            else:
                merged_vt=attr["real_inst_type"]

            vt= [vt for vt in design_config["vt_type"] if vt.lower() in  merged_vt]
            if vt:
                block_name = block_name+'_'+vt[0]
                cell_gen_parameters['vt_type']=vt[0]
            return block_name, cell_gen_parameters
        else:
            logger.debug("No proper parameters found for cell generation")
            block_name = name+"_"+size

    raise NotImplementedError(f"Could not generate LEF for {name}")
