import logging
import plotly.graph_objects as go
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

def dump_blocks(hN, DB, leaves_only=False):
    logger.info(f'hN.parent={hN.parent}')

    fig = go.Figure()

    def gen_trace_xy(inst, prefix_path, child_idx, tr):

        if leaves_only and child_idx >= 0:
            return

        # tr converts local coordinates into global coordinates

        b = inst.originBox
        r = b.LL.x, b.LL.y, b.UR.x, b.UR.y
        [x0, y0, x1, y1] = tr.hitRect(
            transformation.Rect(*r)).canonical().toList()
        x = [x0, x1, x1, x0, x0]
        y = [y0, y0, y1, y1, y0]

        hovertext = f'{"/".join(prefix_path)}<br>{inst.master} ({child_idx})<br>{tr}<br>Global {x0} {y0} {x1} {y1}<br>Local {r[0]} {r[1]} {r[2]} {r[3]}'

        fig.add_trace(go.Scatter(x=x, y=y, mode='lines',
                      name=hovertext, fill="toself", showlegend=False))

    def aux(hN, prefix_path, tr):

        for blk in hN.Blocks:
            child_idx = blk.child
            inst = blk.instance[blk.selectedInstance]

            new_prefix_path = prefix_path + [inst.name]

            # tr converts hN coordinates to global coordinates
            # tr2 = gen_transformation(inst) converts local coordinates to hN coordinates
            # new_tr should be global = tr(tr2(local)

            new_tr = tr.postMult(gen_transformation(inst))

            gen_trace_xy(inst, new_prefix_path, child_idx, new_tr)

            if child_idx >= 0:
                new_hN = DB.hierTree[child_idx]
                aux(new_hN, new_prefix_path, new_tr)

    aux(hN, [], transformation.Transformation())

    fig.update_yaxes(scaleanchor="x", scaleratio=1)
    fig.update_layout(title=dict(text=f'{hN.name}_{hN.n_copy}'))
    fig.show()

