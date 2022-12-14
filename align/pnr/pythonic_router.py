import plotly.graph_objects as go
import plotly.express as px

import logging
import pathlib
import json

from ..cell_fabric import transformation

logger = logging.getLogger(__name__)


def collect_pins(map_d_in, scaled_placement_verilog_d):

    pin_tbl = {}
    for nm, gds_fn in map_d_in:
        pin_tbl[nm] = {}
        with pathlib.Path(gds_fn).with_suffix('.json').open('rt') as fp:
            j = json.load(fp=fp)
            for term in j['terminals']:
                if term['netType'] == 'pin':
                    netName = term['netName']
                    if netName not in pin_tbl[nm]:
                        pin_tbl[nm][netName] = []
                    pin_tbl[nm][netName].append((term['layer'], term['rect']))

    print(pin_tbl)

    colorscale = px.colors.qualitative.Alphabet

    for module in scaled_placement_verilog_d['modules']:
        flat_tbl = {}
        for instance in module['instances']:
            ctn = instance['concrete_template_name']
            tr = transformation.Transformation(**instance['transformation'])
            for fa in instance['fa_map']:
                formal = fa['formal']
                actual = fa['actual']

                if actual not in flat_tbl:
                    flat_tbl[actual] = []

                for layer, rect in pin_tbl[ctn][formal]:
                    newRect = tr.hitRect(transformation.Rect(*rect)).canonical().toList()
                    flat_tbl[actual].append((layer, newRect))

        print(module['concrete_name'], flat_tbl)

        _, _, width, height = module['bbox']
        for idx, (k, v) in enumerate(flat_tbl.items()):
            # color = colorscale[idx % len(colorscale)]

            fig = go.Figure()
            fig.update_xaxes(range=[0,width])
            fig.update_yaxes(
                range=[0,height],
                scaleanchor='x',
                scaleratio=1
            )

            x_lst, y_lst, nm_lst = [], [], []

            layer_colors = {
                'M1': 'red',
                'M2': 'blue',
                'M3': 'green',
                'M4': 'plum',
                'M5': 'brown'
            }

            for layer, rect in v:
                color = layer_colors[layer]
                llx, lly, urx, ury = rect
                fig.add_shape(type="rect", x0=llx, y0=lly, x1=urx, y1=ury, line=dict(color="RoyalBlue", width=1), fillcolor=color)

                x_lst.append(urx)
                y_lst.append(ury)
                nm_lst.append(k)

            fig.add_trace(go.Scatter(x=x_lst, y=y_lst, text=nm_lst, mode="text", textfont=dict(color="black", size=16)))
            fig.show()