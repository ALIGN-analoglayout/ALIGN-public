# Run this app with `python mockup.py` and
# visit http://127.0.0.1:8050/ in your web browser.

import dash
import dash_core_components as dcc
import dash_html_components as html
from dash.dependencies import Input, Output
import itertools
import random

from polish import *

from transformation import Transformation as Tr
from transformation import Rect
from collections import defaultdict

import logging
logging.basicConfig(level=logging.INFO)

import argparse

assert __name__ == '__main__'

parser = argparse.ArgumentParser( description='Mockup of ALIGN UI')
parser.add_argument( '-s', '--block_str', type=str, default='ABCD', help='Blocks to use in enumeration; must only include the characters "ABCEDF"; strings longer than 5 will take a long time')

args = parser.parse_args()

placements, histo, pairs, max_x, max_y = main(args.block_str)

external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']

app = dash.Dash(__name__, external_stylesheets=external_stylesheets)

app.layout = html.Div(
    id='frame',
    children=[
        html.Div(
            children=[
                html.H2(children='Pareto Frontier'),
                dcc.Graph(
                    id='width-vs-height',
                    figure=make_tradeoff_fig(pairs)
                )
            ],
            style={'display': 'inline-block', 'vertical-align': 'top'}
        ),
        html.Div(
            children=[    
                html.H2(children='Placement'),
                dcc.Graph(
                    id='Placement',
                    figure = make_placement_graph(placements, histo, pairs, max_x, max_y,0,0)
                )
            ],
            style={'display': 'inline-block', 'vertical-align': 'top'}
        ),
        html.Div(
            children=[    
                html.H2(children='Tree'),
                dcc.Markdown(children='',id='Tree')
            ],
            style={'display': 'inline-block', 'vertical-align': 'top'}
        )
    ]
)

subindex = 0
prev_idx = None

@app.callback(
    Output('Placement', 'figure'),
    Output('Tree', 'children'),
    Output('width-vs-height', 'clickData'),
    Input('width-vs-height', 'clickData'))
def display_hover_data(clickData):
    global subindex
    global prev_idx

    idx = None
    md_str = ''

    if clickData is not None:
        points = clickData['points']
        assert 1 == len(points)
        idx = points[0]['pointNumber']

        lst = histo[pairs[idx]]

        if prev_idx != idx:
            subindex = 0
        else:
            subindex = (subindex+1)%len(lst)
        ps = lst[subindex]
        prev_idx = idx

        md_str = f"""```text
{polish2tree(ps)}

Polish: {ps}
Coord: {pairs[idx]}
Subindex: {subindex}/{len(lst)}
```
"""

    return make_placement_graph(placements, histo, pairs, max_x, max_y, idx, subindex), md_str, None

app.run_server(debug=True)
