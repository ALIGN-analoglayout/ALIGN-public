import copy
import logging

logger = logging.getLogger(__name__)

def check_floating_pins(verilog_d):
    """exit in case of floating pins in design
    """
    for module in verilog_d["modules"]:
        all_nets = set(fa_map["actual"]  for inst in module["instances"] for fa_map in inst['fa_map'])
        assert set(module["parameters"]).issubset(all_nets), f"floating port found in module {module['name']}"

def check_modules(verilog_d):
    all_module_pins = {}
    for mod in verilog_d["modules"]:
        all_module_pins[mod['name']]=mod["parameters"]
    for mod in verilog_d["modules"]:
        for inst in mod["instances"]:
            assert 'abstract_template_name' in inst, f'no generated data for {inst}'
            if inst["abstract_template_name"] in all_module_pins:
                assert all(fm["formal"] in all_module_pins[inst["abstract_template_name"]] for fm in inst["fa_map"]), \
                    f"incorrect instantiation {inst['instance_name']} of module {inst['abstract_template_name']}, \
                     instance_pins: {inst['fa_map']}, module pins: {all_module_pins[inst['abstract_template_name']]}"

def remove_pg_pins(verilog_d: dict, subckt: str, pg_connections: dict):
    """remove_pg_pins

    Removes any ports related to power pins. PnR engine cannot connect to subcircuit power pins.
    It can connect to a primitive power pin

    Args:
        verilog_d (dict): spice dict from compiler
        subckt (str): name of sub-circuit
        pg_pins (list): list of power pins in subckt to be removed
    """
    logger.debug(f"removing power pins {pg_connections} from subckt {subckt}")
    modules_dict = {module['name']: module['parameters'] for module in verilog_d['modules']}

    if subckt in modules_dict:
        pass
    elif subckt.upper() in modules_dict:
        subckt = subckt.upper()
    else:
        assert False, f"{subckt} not found in design {modules_dict}"
    modules = [module for module in verilog_d['modules'] if module['name'] == subckt]
    assert len(modules) == 1, f"duplicate modules are found {modules}"
    module = modules[0]
    # Remove port from subckt level
    module['parameters'] = [p for p in module['parameters'] if p not in pg_connections.keys()]
    for inst in module['instances']:
        if inst['abstract_template_name'] in modules_dict:
            # Inst pins connected to pg_pins
            hier_pg_connections = {conn["formal"]: pg_connections[conn["actual"]] for conn in inst['fa_map'] if conn["actual"] in pg_connections}
            if len(hier_pg_connections) > 0:
                logger.debug(f"Removing instance {inst['instance_name']} pins connected to {hier_pg_connections}")
                inst['fa_map'] = [conn for conn in inst['fa_map'] if conn["formal"] not in hier_pg_connections]
                # Creates a copy of module with reduced pins
                new_name = modify_pg_conn_subckt(verilog_d, inst['abstract_template_name'], hier_pg_connections)
                inst['abstract_template_name'] = new_name
                remove_pg_pins(verilog_d, new_name, hier_pg_connections)
        else:
            inst['fa_map'] = [{'formal': conn['formal'],
                               'actual': pg_connections.get(conn["actual"], conn["actual"])} for conn in inst['fa_map']]
            logging.debug(f"leaf level node {inst['instance_name']} {inst['abstract_template_name']}")


def clean_if_extra(verilog_d, subckt):
    #Remove modules which are not instantiated
    all_inst = set([inst['abstract_template_name'] for module in verilog_d['modules'] for inst in module["instances"]]+[subckt])
    logger.debug(f"All used modules: {all_inst}")
    verilog_d['modules'] = [m for m in verilog_d['modules'] if m['name'] in all_inst]


def modify_pg_conn_subckt(verilog_d, subckt, pp):
    """
    creates a new subcircuit by removing power pins from a subcircuit definition
    and change internal connections within the subcircuit
    nm: new module
    """
    # TODO: remove redundant const

    nm = copy.copy([module for module in verilog_d['modules'] if module['name'] == subckt][0])

    nm['parameters'] = [p for p in nm['parameters'] if p not in pp]

    logger.debug(f"modifying subckt {nm['name']} {pp}")
    modules_dict = {module['name']: module['parameters'] for module in verilog_d['modules']}
    i = 0
    updated_ckt_name = subckt+'_PG'+str(i)
    while updated_ckt_name in modules_dict.keys():
        if modules_dict[updated_ckt_name] == nm['parameters']:
            logger.debug(f"using existing module {updated_ckt_name}")
            return updated_ckt_name
        else:
            i = i+1
            updated_ckt_name = subckt+'_PG'+str(i)
    nm['name'] = updated_ckt_name

    logger.debug(f"new module is added: {nm}")
    verilog_d['modules'].append(nm)
    return updated_ckt_name
        

def manipulate_hierarchy(verilog_d, subckt):
    check_modules(verilog_d)
    check_floating_pins(verilog_d)
    remove_pg_pins(verilog_d, subckt, {p["actual"]:p["actual"] for p in verilog_d['global_signals']})
    clean_if_extra(verilog_d, subckt)
    check_modules(verilog_d)

