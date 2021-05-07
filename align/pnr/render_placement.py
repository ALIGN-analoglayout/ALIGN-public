import json
import logging
import copy
import pathlib
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

    tr_reflect = transformation.Transformation.genTr( orient, w=blk.width, h=blk.height)

    tr_offset = transformation.Transformation( oX=blk.placedBox.LL.x - blk.originBox.LL.x,
                                               oY=blk.placedBox.LL.y - blk.originBox.LL.y)

    # tr converts local coords into global coordinates
    tr = tr_offset.postMult(tr_reflect)

    logger.debug( f"TRANS {blk.master} {blk.orient} {tr} {tr_reflect} {tr_offset}")
    return tr

def gen_placement_verilog(hN, DB, verilog_d):
    d = verilog_d.copy()

    bboxes = defaultdict(list)
    transforms = defaultdict(list)
    leaf_bboxes = defaultdict(list)

    templates = defaultdict(list)


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
                chosen_master = pathlib.Path(inst.gdsFile).stem
                logger.debug( f'Choose \'{chosen_master}\' for {inst.master} {(hN.name, inst.name)}')
                templates[(hN.name, inst.name)].append( chosen_master)

                leaf_bboxes[chosen_master].append( new_r)

                
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

    for k,v in templates.items():
        if len(set(v)) > 1:
            logger.error( f'Different chosen masters for {k}: {v}')

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
            if k in templates:
                if 'abstract_template_name' not in instance:
                    # Capacitor (internally generated)
                    instance['abstract_template_name'] = instance['template_name']
                    del instance['template_name']

                instance['concrete_template_name'] = templates[k][0]
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

def gen_boxes_and_hovertext( placement_verilog_d, top_cell, sel, leaves_only=False, levels=None):

    leaves = { x['name']: x for x in placement_verilog_d['leaves']}
    modules = { x['name']: x for x in placement_verilog_d['modules']}

    def get_rect( instance):
        # tr converts local coordinates into global coordinates
        if 'template_name' in instance:
            isleaf = False
            template_name = instance['template_name']
            r = modules[template_name]['bbox']
        elif 'concrete_template_name' in instance:
            isleaf = True
            template_name = instance ['concrete_template_name']
            r = leaves[template_name]['bbox']
        else:
            assert False, f'Neither \'template_name\' or \'concrete_template_name\' in inst {instance}.'
        return r, isleaf, template_name

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
            if not leaves_only or isleaf:
                yield gen_trace_xy(r, template_name, new_prefix_path, new_tr)

            if 'template_name' in instance and (levels is None or lvl+1 < levels):
                assert instance['template_name'] in modules
                new_module = modules[instance['template_name']]
                yield from aux(new_module, new_prefix_path, new_tr, lvl+1)

    if top_cell in leaves:
        yield gen_trace_xy(leaves[top_cell]['bbox'], top_cell, (), transformation.Transformation())        
    else:
        yield from aux( modules[top_cell], (), transformation.Transformation(), 0)

def dump_blocks_aux( fig, boxes_and_hovertext):
    for r, hovertext in boxes_and_hovertext:
        [x0, y0, x1, y1] = r
        x = [x0, x1, x1, x0, x0]
        y = [y0, y0, y1, y1, y0]

        fig.add_trace(go.Scatter(x=x, y=y, mode='lines',
                      name=hovertext, fill="toself", showlegend=False))

def dump_blocks( fig, placement_verilog_d, top_cell, sel, leaves_only=False, levels=None):
    logger.info(f'Drawing {top_cell}_{sel}...')

    dump_blocks_aux( fig, gen_boxes_and_hovertext( placement_verilog_d, top_cell, sel, leaves_only=leaves_only, levels=levels))

