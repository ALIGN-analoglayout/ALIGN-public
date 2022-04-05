import copy
import logging
import re
from collections import defaultdict

from ..schema.hacks import List, FormalActualMap

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

def change_concrete_names_for_routing(scaled_placement_verilog_d):
    leaf_ctns = [leaf['concrete_name'] for leaf in scaled_placement_verilog_d['leaves']]

    p = re.compile(r'^(.+)_(\d+)$')
    cn_tbl = defaultdict(list)
    for module in scaled_placement_verilog_d['modules']:
        an = module['abstract_name']
        cn = module['concrete_name']
        m = p.match(cn)
        assert m
        stem, suffix = m.groups()
        assert stem == an
        cn_tbl[an].append(int(suffix))

    tr_tbl = {}
    for an, cn_indices in cn_tbl.items():
        for new_idx, old_idx in enumerate(sorted(cn_indices)):
            tr_tbl[f'{an}_{old_idx}'] = f'{an}_{new_idx}'

    logger.debug(f'change_concrete_names_for_routing: {tr_tbl}')

    for module in scaled_placement_verilog_d['modules']:
        module['concrete_name'] = tr_tbl[module['concrete_name']]
        for instance in module['instances']:
            ctn = instance['concrete_template_name']
            if ctn in leaf_ctns:
                assert ctn not in tr_tbl
                instance['abstract_template_name'] = ctn
            else:
                assert ctn in tr_tbl
                instance['concrete_template_name'] = tr_tbl[ctn]                   

    for leaf in scaled_placement_verilog_d['leaves']:
        leaf['abstract_name'] =leaf['concrete_name']

    return tr_tbl

def gen_abstract_verilog_d( verilog_d):
    new_verilog_d = copy.deepcopy(verilog_d)

    if 'leaves' in new_verilog_d:
        new_verilog_d['leaves'] = None

    for module in new_verilog_d['modules']:
        assert 'concrete_name' in module
        assert 'abstract_name' in module
        assert 'name' not in module
        module['name'] = module['abstract_name']
        del module['abstract_name']        
        del module['concrete_name']        

        assert 'bbox' in module
        del module['bbox']

        for instance in module['instances']:
            assert 'concrete_template_name' in instance
            del instance['concrete_template_name']
            assert 'transformation' in instance
            del instance['transformation']

    return new_verilog_d

def connectivity_change_for_partial_routing(scaled_placement_verilog_d, primitives):
    # Hack scaled_placement_verilog_d in place
    # Update connectivity for partially routed primitives
    if primitives is not None:
        for module in scaled_placement_verilog_d['modules']:
            for instance in module['instances']:
                ctn = instance['concrete_template_name']
                if ctn in primitives:
                    primitive = primitives[ctn]
                    if 'metadata' in primitive and 'partially_routed_pins' in primitive['metadata']:
                        prp = primitive['metadata']['partially_routed_pins']
                        by_net = defaultdict(list)
                        for enity_name, net_name in prp.items():
                            by_net[net_name].append(enity_name)

                        new_fa_map = List[FormalActualMap]()
                        for fa in instance['fa_map']:
                            f, a = fa['formal'], fa['actual'] 
                            for enity_name in by_net.get(f, [f]):
                                new_fa_map.append(FormalActualMap(formal=enity_name, actual=a))

                        instance['fa_map'] = new_fa_map
