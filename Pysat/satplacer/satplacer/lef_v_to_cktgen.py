
from satplacer.lef_parser import LEFParser
from satplacer.verilog_parser import VerilogParser

def convert( lef_str, verilog_str):

    lp = LEFParser()
    lp.parse(lef_str)
    
    vp = VerilogParser()
    vp.parse(verilog_str)

    assert len(vp.modules) == 1
    top_module = vp.modules[0]

    d = { 'nm' : top_module.nm, 'bbox' : [0,0,0,0]}

    lef_map = {}

    leaves = []
    for m in lp.macros:
        assert m.macroName not in lef_map
        lef_map[m.macroName] = m

        leaf = { 'template_name' : m.macroName, 'bbox' : m.bbox }
        terminals = []
        
        for pin in m.pins:
            for port in pin.ports:
                terminal = { 'net_name' : pin.nm, 'layer' : port[0], 'rect' : list(port[1]) }
                terminals.append(terminal)

        leaf['terminals'] = terminals
        leaves.append(leaf)

    d['leaves'] = leaves

    instances = []
    d['instances'] = instances

    for inst in top_module.instances:
        
        assert inst.template_name in lef_map, (inst.template_name, lef_map)
        lef_formals = { pin.nm for pin in lef_map[inst.template_name].pins }
        assert all( formal in lef_formals for (formal,actual) in inst.fa_list), (inst.fa_list, lef_formals)

        instance = { 'template_name' : inst.template_name,
                     'instance_name' : inst.instance_name}

        instance['transformation'] = { 'oX': 0, 'oY': 0, 'sX': 1, 'sY': 1}

        instance['formal_actual_map'] = \
            { formal : actual for (formal, actual) in inst.fa_list}

        instances.append( instance)


    # TODO: global bbox and placement


    return d
