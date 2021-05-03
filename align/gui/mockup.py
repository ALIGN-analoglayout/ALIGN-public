# Run this app with `python mockup.py` and
# visit http://127.0.0.1:8050/ in your web browser.

import dash
import dash_core_components as dcc
import dash_html_components as html
from dash.dependencies import Input, Output

import itertools
import random

from collections import defaultdict

import logging

import pandas as pd

import plotly.graph_objects as go
import plotly.express as px

from ..pnr.render_placement import dump_blocks, gen_placement_verilog

import logging

logger = logging.getLogger(__name__)

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

class AppWithCallbacksAndState:
    def __init__(self, DB, idx, verilog_d, histo):
        external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']
        self.app = dash.Dash(__name__, external_stylesheets=external_stylesheets)

        self.DB = DB
        self.idx = idx
        self.verilog_d = verilog_d
        self.histo = histo

        self.pairs = list(self.histo.keys())

        self.max_x = max( p[0] for p in self.pairs)
        self.max_y = max( p[1] for p in self.pairs)

        self.subindex = 0
        self.prev_idx = None

        self.app.layout = html.Div(
            id='frame',
            children=[
                html.Div(
                    children=[
                        html.H2(children='Pareto Frontier'),
                        dcc.Graph(
                            id='width-vs-height',
                            figure=make_tradeoff_fig(self.pairs)
                        )
                    ],
                    style={'display': 'inline-block', 'vertical-align': 'top'}
                ),
                html.Div(
                    children=[    
                        html.H2(children='Placement'),
                        dcc.Graph(
                            id='Placement',
                            figure = self.make_placement_graph(None)
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

        self.app.callback( (Output('Placement', 'figure'),
                       Output('Tree', 'children'),
                            Output('width-vs-height', 'clickData')),
                      [Input('width-vs-height', 'clickData')])(self.display_hover_data)


    def make_placement_graph( self, sel):
        fig = go.Figure()

        title_d = {}

        if sel is not None:
            hN = self.DB.CheckoutHierNode( self.idx, sel)
            placement_verilog_d = gen_placement_verilog( hN, self.DB, self.verilog_d)

            dump_blocks( fig, placement_verilog_d, hN.name, sel, leaves_only=False)

            title_d = dict(text=f'{hN.name}_{sel}')

        fig.update_layout(
            autosize=False,
            width=800,
            height=800,
            title=title_d
        )

        fig.update_xaxes(
            tickvals=[0,self.max_x],
            range=[0,max(self.max_x,self.max_y)]
        )

        fig.update_yaxes(
            tickvals=[0,self.max_y],
            range=[0,max(self.max_x,self.max_y)]
        )

        return fig



    def display_hover_data(self,clickData):
        md_str = ''
        sel = None
        if clickData is not None:
            points = clickData['points']
            assert 1 == len(points)
            idx = points[0]['pointNumber']

            lst = self.histo[self.pairs[idx]]

            if self.prev_idx != idx:
                self.subindex = 0
            else:
                self.subindex = (self.subindex+1)%len(lst)
            sel = lst[self.subindex]
            self.prev_idx = idx

            md_str = f"""```text
Selection: {sel}
Coord: {self.pairs[idx]}
Subindex: {self.subindex}/{len(lst)}
```

"""

        return self.make_placement_graph(sel), md_str, None


def run_gui( DB, idx, verilog_d, bboxes):
    histo = defaultdict(list)
    for i,p in enumerate(bboxes):
        histo[p].append(i)
    
    awcas = AppWithCallbacksAndState( DB, idx, verilog_d, histo)
    awcas.app.run_server(debug=False)
