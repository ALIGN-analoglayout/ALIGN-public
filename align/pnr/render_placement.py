import json
import logging
import copy
import pathlib
import plotly.graph_objects as go
from itertools import combinations
from collections import defaultdict
from ..cell_fabric import transformation

from .. import PnR

logger = logging.getLogger(__name__)

Omark = PnR.Omark

orient_map = {Omark.FN: 'FN', Omark.FS: 'FS', Omark.N: 'N', Omark.S: 'S'}

def gen_transformation( blk):
    tr_reflect = transformation.Transformation.genTr( orient_map[blk.orient], w=blk.width, h=blk.height)

    tr_offset = transformation.Transformation( oX=blk.placedBox.LL.x - blk.originBox.LL.x,
                                               oY=blk.placedBox.LL.y - blk.originBox.LL.y)

    # tr converts local coords into global coordinates
    tr = tr_offset.postMult(tr_reflect)

    logger.debug( f"TRANS {blk.master} {blk.orient} {tr} {tr_reflect} {tr_offset}")
    return tr

def gen_placement_verilog(hN, idx, sel, DB, verilog_d):
    used_leaves = defaultdict(dict)
    used_internal = defaultdict(dict)

    abstract_template_name = hN.name
    concrete_template_name = f'{abstract_template_name}_{sel}'

    used_internal[abstract_template_name][concrete_template_name] = (idx,sel,(0,0,hN.width,hN.height))

    def traverse( hN, sel):
        for blk in hN.Blocks:
            child_idx = blk.child
            inst = blk.instance[blk.selectedInstance]

            b = inst.originBox
            new_r = b.LL.x, b.LL.y, b.UR.x, b.UR.y

            abstract_template_name = f'{inst.master}'
            if child_idx >= 0:
                concrete_template_name = f'{inst.master}_{blk.selectedInstance}'
                if concrete_template_name not in used_internal[abstract_template_name]:
                    new_hN = DB.CheckoutHierNode(child_idx, blk.selectedInstance)
                    traverse(new_hN, blk.selectedInstance)
                    used_internal[abstract_template_name][concrete_template_name] = (child_idx,blk.selectedInstance,new_r)
                else:
                    assert used_internal[abstract_template_name][concrete_template_name] == (child_idx,blk.selectedInstance,new_r)
            else:
                concrete_template_name = pathlib.Path(inst.gdsFile).stem
                if concrete_template_name not in used_leaves[abstract_template_name]:                
                    used_leaves[abstract_template_name][concrete_template_name] = new_r
                else:
                    assert used_leaves[abstract_template_name][concrete_template_name] == new_r

    traverse( hN, sel)
    logger.debug( f'used_leaves: {used_leaves} used_internal: {used_internal}')

    d = verilog_d.copy()

    modules = []
    for module in d['modules']:
        abstract_name = module['name']
        for concrete_name, (module_idx, module_sel, module_r) in used_internal[abstract_name].items():
           new_module =  module.copy()
           del new_module['name']
           new_module['abstract_name'] = abstract_name
           new_module['concrete_name'] = concrete_name
           new_module['bbox'] = module_r

           new_hN = DB.CheckoutHierNode(module_idx, module_sel)           

           instance_map = { inst['instance_name'] : inst for inst in new_module['instances']}

           for blk in new_hN.Blocks:
               child_idx = blk.child
               inst = blk.instance[blk.selectedInstance]

               instance_d = instance_map[inst.name]
               assert inst.master == instance_d['abstract_template_name']

               if child_idx >= 0:
                   instance_d['concrete_template_name'] = f'{inst.master}_{blk.selectedInstance}'
               else:
                   instance_d['concrete_template_name'] = pathlib.Path(inst.gdsFile).stem

               instance_d['transformation'] = gen_transformation(inst).toDict()

           modules.append(new_module)

    d['modules'] = modules

    d['leaves'] = [{'abstract_name': a, 'concrete_name': c, 'bbox': r} for a, v in used_leaves.items() for c, r in v.items()]

    #print(d.json(indent=2))

    return d

def scalar_rational_scaling( v, *, mul=1, div=1):
    if type(mul) == float:
        return mul*v/div
    else:
        q, r = divmod( mul*v, div)
        assert r == 0
        return q

def array_rational_scaling( a, *, mul=1, div=1):
    return [ scalar_rational_scaling(v, mul=mul, div=div) for v in a]

def scale_placement_verilog( placement_verilog_d, scale_factor):
    # Convert from 0.5 nm to 0.1 nm if the scale_factor is 10
    d = copy.deepcopy(placement_verilog_d)

    for module in d['modules']:
        module['bbox'] = array_rational_scaling(module['bbox'], mul=scale_factor, div=2)
        for instance in module['instances']:
            tr = instance['transformation'] 
            for field in ['oX','oY']:
                tr[field] = scalar_rational_scaling(tr[field], mul=scale_factor, div=2)

    for leaf in d['leaves']:
        leaf['bbox'] = array_rational_scaling(leaf['bbox'], mul=scale_factor, div=2)

    return d


def gen_boxes_and_hovertext( placement_verilog_d, top_cell):

    leaves = { x['concrete_name']: x for x in placement_verilog_d['leaves']}
    modules = { x['concrete_name']: x for x in placement_verilog_d['modules']}

    def get_rect( instance):
        ctn = instance ['concrete_template_name']
        if ctn in leaves:
            r = leaves[ctn]['bbox']
            return r, True, ctn
        else:
            r = modules[ctn]['bbox']
            return r, False, ctn

    def gen_trace_xy(r, template_name, prefix_path, tr):

        [x0, y0, x1, y1] = tr.hitRect(
            transformation.Rect(*r)).canonical().toList()
 
        hovertext = f'{"/".join(prefix_path)}<br>{template_name}<br>{tr}<br>Global {x0} {y0} {x1} {y1}<br>Local {r[0]} {r[1]} {r[2]} {r[3]}'

        return [x0, y0, x1, y1], hovertext


    def aux(module, prefix_path, tr, lvl):

        for instance in module['instances']:
            new_prefix_path = prefix_path + (instance['instance_name'],)

            # tr converts module coordinates to global coordinates
            # local_tr converts local coordinates to module coordinates
            # new_tr should be global = tr(local_tr(local))

            local_tr = transformation.Transformation( **instance['transformation'])
            new_tr = tr.postMult(local_tr)

            r, isleaf, template_name = get_rect(instance)
            yield gen_trace_xy(r, template_name, new_prefix_path, new_tr) + (isleaf, lvl)

            ctn = instance['concrete_template_name']
            if ctn in modules:
                yield from aux(modules[ctn], new_prefix_path, new_tr, lvl+1)

    if top_cell in leaves:
        yield gen_trace_xy(leaves[top_cell]['bbox'], top_cell, (), transformation.Transformation()) + (True, 0)
    elif top_cell in modules:
        yield from aux( modules[top_cell], (), transformation.Transformation(), 0)
    else:
        logger.warning( f'{top_cell} not in either leaves or modules.')

def standalone_overlap_checker( placement_verilog_d, top_cell):
    def rects_overlap( rA, rB):
        return max( rA[0], rB[0]) < min( rA[2], rB[2]) and max( rA[1], rB[1]) < min( rA[3], rB[3])
        #return rA[0] < rB[2] and rB[0] < rA[2] and rA[1] < rB[3] and rB[1] < rA[3]

    leaves = [ r for r, _, isleaf, _ in gen_boxes_and_hovertext( placement_verilog_d, top_cell) if isleaf]
    logger.debug( f'Checking {len(leaves)} bboxes for overlap')
    for a,b in combinations(leaves,2):
        if rects_overlap( a, b):
            logger.error( f'Leaves {a} and {b} intersect')

def dump_blocks( fig, boxes_and_hovertext, leaves_only, levels):
    for r, hovertext, isleaf, lvl in boxes_and_hovertext:
        if leaves_only and not isleaf:
            continue
        if levels is not None and lvl >= levels:
            continue

        [x0, y0, x1, y1] = r
        x = [x0, x1, x1, x0, x0]
        y = [y0, y0, y1, y1, y0]

        fig.add_trace(go.Scatter(x=x, y=y, mode='lines',
                      name=hovertext, fill="toself", showlegend=False))

