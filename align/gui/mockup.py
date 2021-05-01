# Run this app with `python mockup.py` and
# visit http://127.0.0.1:8050/ in your web browser.

import dash
import dash_core_components as dcc
import dash_html_components as html
from dash.dependencies import Input, Output
import plotly.graph_objects as go
import plotly.express as px
import pandas as pd
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

def make_placement_graph(idx,subindex):
    fig = go.Figure()

    if idx is None:
        return fig

    colors = {'A': 'Plum', 'B': 'Khaki', 'C': 'SpringGreen', 'D': 'Salmon', 'E': 'SteelBlue', 'F': 'yellow',
              'w0': 'rgb( 255, 255, 255)',
              'w1': 'rgb( 240, 255, 255)',
              'w2': 'rgb( 255, 240, 255)',
              'w3': 'rgb( 255, 255, 240)',
              'w4': 'rgb( 255, 240, 240)'}

    s = histo[pairs[idx]][subindex]

    for named_rect in placements[s]:
        nm, [x0, y0, x1, y1] = named_rect
        x = [x0, x1, x1, x0, x0]
        y = [y0, y0, y1, y1, y0]
        fig.add_trace( go.Scatter(x=x, y=y,
                                   mode='lines', fill='toself',
                                   fillcolor=colors.get(nm,'yellow'),
                                   showlegend=False,
                                   name=f'{nm}'))

    fig.update_layout(
        autosize=False,
        width=800,
        height=800
    )

    fig.update_xaxes(
        tickvals=[0,max_x],
        range=[0,max(max_x,max_y)]
    )

    fig.update_yaxes(
        tickvals=[0,max_y],
        range=[0,max(max_x,max_y)]
    )

    return fig



parser = argparse.ArgumentParser( description='Mockup of ALIGN UI')
parser.add_argument( '-s', '--block_str', type=str, default='ABCD', help='Blocks to use in enumeration; must only include the characters "ABCEDF"; strings longer than 5 will take a long time')

args = parser.parse_args()

placements, histo, pairs, max_x, max_y = main(args.block_str)

def make_tradeoff_fig(pairs):

    df = pd.DataFrame( data=pairs, columns=['width','height'])
    fig = px.scatter(df, x="width", y="height", width=800, height=800)

    fig.update_traces( marker=dict(size=10))
    fig.update_xaxes(
        rangemode="tozero"
    )
    fig.update_yaxes(
        rangemode="tozero",
        scaleanchor='x',
        scaleratio = 1
    )

    return fig

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
                    figure = make_placement_graph(0,0)
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

    fig = make_placement_graph(idx, subindex)

    return fig, md_str, None

app.run_server(debug=True)
