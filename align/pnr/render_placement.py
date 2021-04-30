import json
import logging
import copy
import plotly.graph_objects as go
from collections import defaultdict
from ..cell_fabric import transformation

from .. import PnR

logger = logging.getLogger(__name__)

Omark = PnR.Omark

def gen_transformation( blk):
    if blk.orient == Omark.FN:
        orient = 'FN'
    elif blk.orient == Omark.FS:
        orient = 'FS'
    elif blk.orient == Omark.N:
        orient = 'N'
    elif blk.orient == Omark.S:
        orient = 'S'
    else:
        assert False, blk.orient

    # tr is the reflection part
    tr = transformation.Transformation.genTr( orient, w=blk.width, h=blk.height)

    # tr2 is the translation part
    tr2 = transformation.Transformation( oX=blk.placedBox.UR.x - blk.originBox.LL.x,
                                         oY=blk.placedBox.UR.y - blk.originBox.LL.y)

    # tr3 converts local coords into global coordinates
    tr3 = tr.preMult(tr2)

    logger.debug( f"TRANS {blk.master} {blk.orient} {tr} {tr2} {tr3}")
    return tr3

def gen_placement_verilog(hN, DB, verilog_d):
    d = verilog_d.copy()

    bboxes = defaultdict(list)
    transforms = defaultdict(list)
    leaf_bboxes = defaultdict(list)

    def aux(hN, r, prefix_path):

        bboxes[prefix_path[-1][1]].append( r)

        for blk in hN.Blocks:
            child_idx = blk.child
            inst = blk.instance[blk.selectedInstance]

            tr = gen_transformation(inst)            

            new_prefix_path = prefix_path + ((inst.name,inst.master),)
            k = new_prefix_path[-2][1], new_prefix_path[-1][0]
            transforms[k].append( tr)

            b = inst.originBox
            new_r = b.LL.x, b.LL.y, b.UR.x, b.UR.y
            if child_idx >= 0:
                new_hN = DB.CheckoutHierNode(child_idx, blk.selectedInstance)
                aux(new_hN, new_r, new_prefix_path)
            else:
                leaf_bboxes[inst.master].append( new_r)

                
    r = 0, 0, hN.width, hN.height
    aux(hN, r, (('',hN.name),))

    for k,v in transforms.items():
        if len(set(v)) > 1:
            logger.error( f'Different transforms for {k}: {v}')

    for k,v in bboxes.items():
        if len(set(v)) > 1:
            logger.error( f'Different bboxes for {k}: {v}')

    for k,v in leaf_bboxes.items():
        if len(set(v)) > 1:
            logger.error( f'Different leaf bboxes for {k}: {v}')

    logger.debug( f'transforms: {transforms}')
    logger.debug( f'bboxes: {bboxes}')
    logger.debug( f'leaf_bboxes: {leaf_bboxes}')

    for module in d['modules']:
        nm = module['name']
        if nm in bboxes:
            module['bbox'] = bboxes[nm][0]
        else:
            logger.error( f'No bounding box for module {nm}')
        for instance in module['instances']:
            k = (nm, instance['instance_name']) 
            if k in transforms:
                instance['transformation'] = transforms[k][0].toDict()
            else:
                logger.error( f'No transform for instance {k[0]} in {k[1]}')

    leaves = []
    for k, v in leaf_bboxes.items():
        leaf = {}
        leaf['name'] = k
        leaf['bbox'] = v[0]
        leaves.append(leaf)

    d['leaves'] = leaves

    #print( json.dumps( d, indent=2))

    return d

def dump_blocks2( placement_verilog_d, top_cell, sel, leaves_only=False):
    logger.info(f'Drawing {top_cell}_{sel}...')

    fig = go.Figure()

    leaves = { x['name']: x for x in placement_verilog_d['leaves']}
    modules = { x['name']: x for x in placement_verilog_d['modules']}

    def gen_trace_xy(instance, prefix_path, tr):
        # tr converts local coordinates into global coordinates

        template_name = instance['template_name']

        if leaves_only and template_name in modules:
            return

        if template_name in leaves:
            r = leaves[template_name]['bbox']
        elif template_name in modules:
            r = modules[template_name]['bbox']
        else:
            assert False, template_name

        [x0, y0, x1, y1] = tr.hitRect(
            transformation.Rect(*r)).canonical().toList()
        x = [x0, x1, x1, x0, x0]
        y = [y0, y0, y1, y1, y0]

        hovertext = f'{"/".join(prefix_path)}<br>{template_name}<br>{tr}<br>Global {x0} {y0} {x1} {y1}<br>Local {r[0]} {r[1]} {r[2]} {r[3]}'

        fig.add_trace(go.Scatter(x=x, y=y, mode='lines',
                      name=hovertext, fill="toself", showlegend=False))


    def aux(module, prefix_path, tr):

        for instance in module['instances']:

            new_prefix_path = prefix_path + (instance['instance_name'],)

            # tr converts module coordinates to global coordinates
            # local_tr converts local coordinates to module coordinates
            # new_tr should be global = tr(local_tr(local))

            local_tr = transformation.Transformation( **instance['transformation'])
            new_tr = tr.postMult(local_tr)

            gen_trace_xy(instance, new_prefix_path, new_tr)

            if instance['template_name'] in modules:
                new_module = modules[instance['template_name']]
                aux(new_module, new_prefix_path, new_tr)

    aux( modules[top_cell], (), transformation.Transformation())


    fig.update_yaxes(scaleanchor="x", scaleratio=1)
    fig.update_layout(title=dict(text=f'{top_cell}_{sel}'))
    fig.show()

