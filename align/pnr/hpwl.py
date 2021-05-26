
import logging
import pathlib
from collections import defaultdict


from .. import PnR
from ..cell_fabric.transformation import Transformation, Rect

logger = logging.getLogger(__name__)

def calculate_HPWL_from_hN( hN):

    HPWL = 0

    logger_fn = logger.debug

    for neti in hN.Nets:

        mx, Mx, my, My = None, None, None, None

        logger_fn( f'Working on {neti.name}')

        for connectedj in neti.connected:
            ntype,iter2,iter = connectedj.type, connectedj.iter2, connectedj.iter

            if ntype == PnR.NType.Terminal: continue

            blk = hN.Blocks[iter2]
            inst = blk.instance[blk.selectedInstance]

            gdsFile = pathlib.Path(inst.gdsFile).stem

            logger_fn( f'{hN.name} neti {ntype,iter2,iter} {inst.master} {inst.name} {gdsFile} {blk.selectedInstance}')
            for contact in inst.blockPins[iter].pinContacts:
                b = contact.placedBox
                bc = b.center()
                c = contact.placedCenter
                logger_fn( f'{c.x} {c.y} {bc.x} {bc.y}')
                assert c.x == bc.x and c.y == bc.y

                if mx is None or mx > c.x: mx = c.x
                if Mx is None or Mx < c.x: Mx = c.x
                if my is None or my > c.y: my = c.y
                if My is None or My < c.y: My = c.y
                    
        net_HPWL = Mx-mx + My-my if mx is not None else 0

        logger_fn( f'{net_HPWL}')
        logger_fn( f'==========')

        HPWL += net_HPWL
    return HPWL

def gen_netlist( placement_verilog_d, concrete_name):
    nets_d = defaultdict(list)

    modules = { module['concrete_name']: module for module in placement_verilog_d['modules']}

    def aux( module, prefix_path, translate_d):

        parameters = { net for net in module['parameters']}

        for k, _ in translate_d.items():
            assert k in parameters

        if prefix_path != ():
            for p in parameters:
                assert p in translate_d


        for inst in module['instances']:
            instance_name = inst['instance_name']
            ctn = inst['concrete_template_name']
            if ctn in modules: # non-leaf
                new_translate_d = {}
                for fa in inst['fa_map']:
                    f = fa['formal']
                    a = fa['actual']
                    new_a = translate_d.get(a,prefix_path + (a,))
                    new_translate_d[f] = new_a

                aux( modules[ctn], prefix_path + (instance_name,), new_translate_d)

            else: #leaf
                for fa in inst['fa_map']:
                    f = fa['formal']
                    a = fa['actual']
                    new_a = translate_d.get(a,prefix_path + (a,))
                    nets_d[new_a].append(prefix_path + (instance_name,f))


    aux( modules[concrete_name], (), {})

    return nets_d


def calculate_HPWL_from_placement_verilog_d( placement_verilog_d, concrete_name, nets_d):

    """Two ways to do this. Compute hierarchically or virtually flat."""

    """Find all the leaf terminals"""

    nets_d = gen_netlist( placement_verilog_d, concrete_name)
    modules = { module['concrete_name']: module for module in placement_verilog_d['modules']}
    instances = { (module['concrete_name'],instance['instance_name']): instance for module in placement_verilog_d['modules'] for instance in module['instances']}

    leaf_terminals = defaultdict(list)

    for leaf in placement_verilog_d['leaves']:
        ctn = leaf['concrete_name']
        for terminal in leaf['terminals']:
            leaf_terminals[(ctn,terminal['name'])].append( terminal['rect'])

    logger_fn = logger.debug

    HPWL = 0

    for hnet, hpins in nets_d.items():

        mx, Mx, my, My = None, None, None, None

        for hpin in hpins:
            ctn = concrete_name
            tr = Transformation()
            for instance_name in hpin[:-1]:
                instance = instances[(ctn,instance_name)]
                ctn = instance['concrete_template_name']
                tr = tr.postMult(Transformation( **instance['transformation']))
            
            for r in leaf_terminals[(ctn,hpin[-1])]:
                [x0, y0, x1, y1] = tr.hitRect( Rect(*r)).canonical().toList()

                #[x0, y0, x1, y1] = [ (x0+x1)//2, (y0+y1)//2, (x0+x1)//2, (y0+y1)//2]

                logger_fn(f'terminal: {x0,y0,x1,y1}')

                if mx is None or x0 < mx: mx = x0
                if Mx is None or Mx < x1: Mx = x1
                if my is None or y0 < my: my = y0
                if My is None or My < y1: My = y1

        local_HPWL = Mx-mx + My-my if mx is not None else 0

        logger_fn( f"from netlist HPWL: {'/'.join(hnet)}: {local_HPWL}")

        HPWL += local_HPWL

    return HPWL
