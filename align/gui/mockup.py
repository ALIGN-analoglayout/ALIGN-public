# Run this app with `python mockup.py` and
# visit http://127.0.0.1:8050/ in your web browser.

import dash
import dash_core_components as dcc
import dash_html_components as html
from dash.dependencies import Input, Output

import math
import numpy as np

from collections import defaultdict

import logging

import pandas as pd

import plotly.graph_objects as go
import plotly.express as px

from ..pnr.render_placement import dump_blocks3, gen_placement_verilog


import logging

logger = logging.getLogger(__name__)

def make_tradeoff_fig(pairs, log=False, scale='Blugrn'):

    df = pd.DataFrame( data=pairs, columns=['width','height'])
    df['area'] = df['width']*df['height']
    df['aspect_ratio'] = df['height'] / df['width']

    df['ordering'] = np.arange(len(df))
    df['size'] = len(df) - np.arange(len(df))


    fig = px.scatter(
        df,
        x="width",
        y="height",
        color="ordering",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800
    )

    area = df['area'].min()

    min_width, max_width = min(df['width']),max(df['width'])
    min_height, max_height = min(df['height']),max(df['height'])

    sweep_width = np.linspace( min_width, max_width, 101)
    sweep_height = area/sweep_width

    fig.add_trace(
        go.Scatter( 
            x=sweep_width,
            y=sweep_height,
            mode='lines',
            showlegend=False
        )
    )

    #fig.update_traces( marker=dict(size=10))

    if log:

        log_min = min( math.log10(min_width), math.log10(min_height)) - 0.01
        log_max = max( math.log10(max_width), math.log10(max_height)) + 0.01

        fig.update_xaxes(
            type="log",
            range=[log_min,log_max]
        )
        fig.update_yaxes(
            type="log",
            range=[log_min,log_max],
            scaleanchor='x',
            scaleratio = 1
        )

    else:

        linear_min = 0
        linear_max = max( max_width, max_height) * 1.1

        fig.update_xaxes(
            range=[linear_min,linear_max]
        )
        fig.update_yaxes(
            range=[linear_min,linear_max],
            scaleanchor='x',
            scaleratio = 1
        )


    return fig


colorscales = ['Blugrn'] + px.colors.named_colorscales() 

class AppWithCallbacksAndState:
    def __init__(self, DB, idx, verilog_d, histo, opath):
        self.DB = DB
        self.idx = idx
        self.verilog_d = verilog_d
        self.histo = histo
        self.opath = opath

        external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']
        self.app = dash.Dash(__name__, external_stylesheets=external_stylesheets)

        self.sel = None

        self.module_names = [ module['name'] for module in self.verilog_d['modules']]

        self.pairs = list(self.histo.keys())

        self.max_x = max( p[0] for p in self.pairs)
        self.max_y = max( p[1] for p in self.pairs)

        self.subindex = 0
        self.prev_idx = None

        self.tradeoff = make_tradeoff_fig(self.pairs, log=True)

        self.app.layout = html.Div(
            id='frame',
            children=[
                html.Div(
                    children=[
                        html.H2(children='Pareto Frontier'),
                        dcc.Dropdown(
                            id='colorscale', 
                            options=[{"value": x, "label": x} 
                                     for x in colorscales],
                            value='Blugrn',
                            style={ 'width': '350px'}
                        ),
                        dcc.RadioItems(
                            id='axes-type',
                            options=[{'label': i, 'value': i} for i in ['linear', 'loglog']],
                            value='loglog',
                            labelStyle={'display': 'inline-block'}
                        ),
                        dcc.Dropdown(
                            id='module-name', 
                            options=[{"value": x, "label": x} 
                                     for x in self.module_names],
                            value=self.DB.hierTree[self.idx].name,
                            style={ 'width': '350px'}
                        ),
                        dcc.Graph(
                            id='width-vs-height',
                            figure=self.tradeoff
                        )
                    ],
                    style={'display': 'inline-block', 'vertical-align': 'top'}
                ),
                html.Div(
                    children=[    
                        html.H2(children='Placement'),
                        dcc.RadioItems(
                            id='display-type',
                            options=[{'label': i, 'value': i} for i in ['All', 'Direct', 'Leaves Only']],
                            value='All',
                            labelStyle={'display': 'inline-block'}
                        ),
                        html.Button(
                            'Route',
                            id='route-current',
                            n_clicks=0
                        ),
                        dcc.Graph(
                            id='Placement',
                            figure = self.make_placement_graph()
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
                ),
                html.Div(
                    children=[    
                    ],
                    style={'display': 'inline-block', 'vertical-align': 'top'}
                )
            ]
        )

        self.app.callback( (Output('Placement', 'figure'),
                            Output('Tree', 'children'),
                            Output('width-vs-height', 'clickData')),
                      [Input('width-vs-height', 'clickData'),
                       Input('width-vs-height', 'hoverData'),
                       Input('display-type', 'value')])(self.display_hover_data)

        self.app.callback( (Output('route-current', 'n_clicks'),),
                           [Input('route-current', 'n_clicks')])(self.route_current_placement)

        self.app.callback( (Output('width-vs-height', 'figure'),),
                           [Input('colorscale', 'value'),
                            Input('axes-type', 'value'),
                            Input('module-name', 'value')])(self.change_colorscale)

    def make_placement_graph( self, sel=None, *, display_type='All'):
        if display_type == 'All':
            levels = None
            leaves_only = False
        elif display_type == 'Direct':
            levels = 0
            leaves_only = False
        elif display_type == 'Leaves Only':
            leaves_only = True
            levels = None
        else:
            assert False, display_type

        fig = go.Figure()
        title_d = {}

        if sel is not None:
            hN = self.DB.CheckoutHierNode( self.idx, sel)
            placement_verilog_d = gen_placement_verilog( hN, self.DB, self.verilog_d)
            dump_blocks3( fig, placement_verilog_d, hN.name, sel, leaves_only=leaves_only, levels=levels)
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

    def change_colorscale(self, scale, axes_type, module_name):
        # Should get a diffent set of pairs for a different module name

        self.tradeoff = make_tradeoff_fig(self.pairs, log=axes_type == 'loglog', scale=scale)
        return (self.tradeoff,)

    def route_current_placement(self, n_clicks):
        if self.sel is not None:
            print( f'Start the router using sel {self.sel}')
            from ..pnr.toplevel import route
            route( DB=self.DB, idx=self.idx, opath=self.opath, adr_mode=False, PDN_mode=False, router_mode='top_down')

        return (0,)

    def display_hover_data(self,clickData,hoverData,display_type):
        md_str = ''
        sel = None

        ctx = dash.callback_context
        if ctx.triggered:
            d = ctx.triggered[0]
            if d['prop_id'] == 'display-type.value':
                sel = self.sel
                md_str = self.md_str
            if d['prop_id'] == 'width-vs-height.clickData':
                pass
            if d['prop_id'] == 'width-vs-height.hoverData':
                pass


        if clickData is not None:
            points = clickData['points']
            assert 1 == len(points)
            idx = points[0]['pointNumber']

        if hoverData is not None:
            points = hoverData['points']
            assert 1 == len(points)
            idx = points[0]['pointNumber']


        if clickData is not None or hoverData is not None:

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
            self.sel = sel
            self.md_str = md_str

        return self.make_placement_graph(sel,display_type=display_type), md_str, None


def run_gui( DB, idx, verilog_d, bboxes, opath):
    # this could probably be done in pandas
    histo = defaultdict(list)
    for i,p in enumerate(bboxes):
        histo[p].append(i)
    
    AppWithCallbacksAndState( DB, idx, verilog_d, histo, opath).app.run_server(debug=False)
