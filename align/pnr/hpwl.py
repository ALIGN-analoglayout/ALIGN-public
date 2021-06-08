
import logging
import pathlib
from collections import defaultdict


from .. import PnR
from ..cell_fabric.transformation import Transformation, Rect
from .render_placement import gen_transformation

logger = logging.getLogger(__name__)

class Interval:
    def __init__(self):
        self.m, self.M = None, None

    def add(self, v):
        if self.m is None or v < self.m:
            self.m = v
        if self.M is None or v > self.M:
            self.M = v
        
    def dist(self):
        return (self.M - self.m) if self.m is not None else 0

    def __repr__(self):
        return f'Interval(dist={self.dist()},m={self.m},M={self.M})'

class SemiPerimeter:
    def __init__(self):
        self.ix = Interval()
        self.iy = Interval()
        
    def addPoint(self, p):
        x,y = p
        self.ix.add( x)
        self.iy.add( y)

    def addRect(self, r):
        x0,y0,x1,y1 = r
        self.ix.add( x0)
        self.ix.add( x1)
        self.iy.add( y0)
        self.iy.add( y1)
        
    def dist(self):
        return self.ix.dist() + self.iy.dist()

    def __repr__(self):
        return f'SemiPerimeter(dist={self.dist()},ix={self.ix},iy={self.iy})'

    def toList(self):
        assert self.ix.m is not None
        return [self.ix.m,self.iy.m,self.ix.M,self.iy.M]

def calculate_HPWL_from_hN( hN):

    HPWL = 0

    for neti in hN.Nets:

        sp = SemiPerimeter()

        logger.debug( f'Working on {neti.name}')

        for connectedj in neti.connected:
            ntype,iter2,iter = connectedj.type, connectedj.iter2, connectedj.iter

            if ntype == PnR.NType.Terminal: continue

            blk = hN.Blocks[iter2]
            inst = blk.instance[blk.selectedInstance]

            tr = Transformation( **gen_transformation(inst).toDict())

            gdsFile = pathlib.Path(inst.gdsFile).stem

            logger.debug( f'{hN.name} neti {ntype,iter2,iter} {inst.master} {inst.name} {gdsFile} {blk.selectedInstance}')
            for contact in inst.blockPins[iter].pinContacts:
                ob = contact.originBox
                new_b = tr.hitRect(Rect( ob.LL.x, ob.LL.y, ob.UR.x, ob.UR.y)).canonical().toList()

                b = contact.placedBox

                assert new_b[0] == b.LL.x and new_b[1] == b.LL.y and new_b[2] == b.UR.x and new_b[3] == b.UR.y

                bc = b.center()
                c = contact.placedCenter

                assert 2*c.x == b.LL.x + b.UR.x
                assert 2*c.y == b.LL.y + b.UR.y

                logger.debug( f'{c.x} {c.y} {bc.x} {bc.y}')
                assert c.x == bc.x and c.y == bc.y

                sp.addPoint( (c.x, c.y))
                    
        net_HPWL = sp.dist()

        logger.debug( f'{neti.name} {net_HPWL} {sp}')
        logger.debug( f'==========')

        HPWL += net_HPWL
    return HPWL

def gen_netlist( placement_verilog_d, concrete_name):
    nets_d = defaultdict(list)

    modules = { module['concrete_name']: module for module in placement_verilog_d['modules']}
    global_actuals = { gs['actual'] for gs in placement_verilog_d['global_signals']}

    def aux( module, prefix_path, translate_d):

        parameters = { net for net in module['parameters']}

        for k, _ in translate_d.items():
            assert k in parameters

        if prefix_path != ():
            for p in parameters:
                assert p in translate_d

        for inst in module['instances']:
            def gen_pair():
                for fa in inst['fa_map']:
                    f,a = fa['formal'], fa['actual']
                    new_a = (a,) if a in global_actuals else translate_d.get(a,prefix_path + (a,))
                    yield f, new_a

            instance_name = inst['instance_name']
            ctn = inst['concrete_template_name']
            if ctn in modules: # non-leaf
                aux( modules[ctn], prefix_path + (instance_name,), dict( gen_pair()))
            else: #leaf
                for f,new_a in gen_pair():
                    nets_d[new_a].append(prefix_path + (instance_name,f))


    aux( modules[concrete_name], (), {})

    return nets_d

def to_center( r):
    #xc = (r[0]+r[2])//2
    #yc = (r[1]+r[3])//2
    #return [xc,yc,xc,yc]
    return r

def calculate_HPWL_from_placement_verilog_d_top_down( placement_verilog_d, concrete_name, nets_d):
    instances = { (module['concrete_name'],instance['instance_name']): instance for module in placement_verilog_d['modules'] for instance in module['instances']}

    leaf_terminals = defaultdict(list)

    for leaf in placement_verilog_d['leaves']:
        ctn = leaf['concrete_name']
        for terminal in leaf['terminals']:
            leaf_terminals[(ctn,terminal['name'])].append( to_center(terminal['rect']))

    HPWL = 0
    for hnet, hpins in nets_d.items():
        sp = SemiPerimeter()
        for hpin in hpins:
            ctn = concrete_name
            tr = Transformation()
            for instance_name in hpin[:-1]:
                instance = instances[(ctn,instance_name)]
                ctn = instance['concrete_template_name']
                tr = tr.postMult(Transformation( **instance['transformation']))
            
            for r in leaf_terminals[(ctn,hpin[-1])]:
                new_r = tr.hitRect( Rect(*r)).canonical().toList()
                if hnet == ('vss',):
                    logger.debug(f'terminal: {new_r}')
                sp.addRect( new_r)

        local_HPWL = sp.dist()
        logger.debug( f"from netlist HPWL: {'/'.join(hnet)}: {local_HPWL}")
        HPWL += local_HPWL

    return HPWL

def compute_topoorder( modules, concrete_name):
    found_modules, found_leaves = set(), set()
    order = []
    def aux( cn):
        if cn in modules:
            found_modules.add( cn)
            for instance in modules[cn]['instances']:        
                ctn = instance['concrete_template_name']
                if ctn not in found_modules and ctn not in found_leaves:
                    aux( ctn)
            order.append( cn)
        else:
            found_leaves.add(cn)
            order.append( cn)
    aux(concrete_name)
    return order, found_modules, found_leaves

def calculate_HPWL_from_placement_verilog_d_bottom_up( placement_verilog_d, concrete_name):

    modules = { module['concrete_name']: module for module in placement_verilog_d['modules']}

    global_actuals = { gs['actual'] for gs in placement_verilog_d['global_signals']}

    leaf_terminals = defaultdict(list)

    for leaf in placement_verilog_d['leaves']:
        ctn = leaf['concrete_name']
        for terminal in leaf['terminals']:
            leaf_terminals[(ctn,terminal['name'])].append( to_center(terminal['rect']))

    order, found_modules, found_leaves = compute_topoorder( modules, concrete_name)

    net_bboxes = defaultdict(SemiPerimeter)
    net_local_hpwls = {}

    for k, v in leaf_terminals.items():
        for r in v:
            net_bboxes[k].addRect( r)

    for cn in order:
        if cn in found_modules:
            logger.debug( f'Working on {cn}')
            module = modules[cn]

            local_hpwl = 0

            local_a = set()
            for instance in module['instances']:
                ctn = instance['concrete_template_name']

                if ctn in net_local_hpwls:
                    local_hpwl += net_local_hpwls[ctn]

                tr = Transformation( **instance['transformation'])
                for fa in instance['fa_map']:
                    f, a = fa['formal'], fa['actual']
                    new_r = tr.hitRect(Rect(*net_bboxes[(ctn,f)].toList())).canonical().toList()
                    local_a.add(a)

                    net_bboxes[(cn,a)].addRect( new_r)

                for a in global_actuals:
                    if (ctn,a) in net_bboxes:
                        new_r = tr.hitRect(Rect(*net_bboxes[(ctn,a)].toList())).canonical().toList()
                        net_bboxes[(cn,a)].addRect( new_r)

            for a in local_a.difference(set( module['parameters']).union(global_actuals)):
                net_hpwl = net_bboxes[(cn,a)].dist()
                logger.debug( f'Accounting for hidden net {a} {net_hpwl} in {cn}')
                local_hpwl += net_hpwl
            
            net_local_hpwls[cn] = local_hpwl


    assert order[-1] == concrete_name

    cn = concrete_name
    module = modules[cn]

    HPWL = net_local_hpwls[cn]
    for a in set(module['parameters']).union(global_actuals):
        net_hpwl = net_bboxes[(cn,a)].dist()
        logger.debug( f'Accounting for top-level (or global) net {a} {net_hpwl} in {cn}')
        HPWL += net_hpwl
        
    return HPWL

def calculate_HPWL_from_placement_verilog_d( placement_verilog_d, concrete_name, nets_d):
    return 0.
    hpwl_top_down = calculate_HPWL_from_placement_verilog_d_top_down( placement_verilog_d, concrete_name, nets_d)
    hpwl_bottom_up = calculate_HPWL_from_placement_verilog_d_bottom_up( placement_verilog_d, concrete_name)

    if hpwl_top_down != hpwl_bottom_up:
        logger.warning( f'HPWL calculated in different ways differ: top_down: {hpwl_top_down} bottom_up: {hpwl_bottom_up}')

    return hpwl_bottom_up
