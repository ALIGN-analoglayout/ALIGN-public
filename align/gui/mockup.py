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

from ..pnr.render_placement import dump_blocks


import logging

logger = logging.getLogger(__name__)



def make_tradeoff_fig_wh(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="width",
        y="height",
        color="ordering",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['aspect_ratio','area']
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

def make_tradeoff_fig_aa(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="aspect_ratio",
        y="area",
        color="ordering",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['width','height']
    )

    area = df['area'].min()

    min_x, max_x = min(df['aspect_ratio']),max(df['aspect_ratio'])
    min_y, max_y = min(df['area']),max(df['area'])

    sweep_x = np.linspace( min_x, max_x, 101)
    sweep_y = area+0*sweep_x

    fig.add_trace(
        go.Scatter( 
            x=sweep_x,
            y=sweep_y,
            mode='lines',
            showlegend=False
        )
    )

    if log:
        fig.update_xaxes(
            type="log"
        )
        fig.update_yaxes(
            type="log"
        )
    else:
        fig.update_xaxes(
        )
        fig.update_yaxes(
        )

    return fig

def make_tradeoff_fig( axes, df, log=False, scale='Blugrn'):
    if   axes == ('width', 'height'):
        return make_tradeoff_fig_wh( df, log, scale)
    elif axes == ('aspect_ratio', 'area'):
        return make_tradeoff_fig_aa( df, log, scale)
    else:
        assert False, axes

colorscales = ['Blugrn'] + px.colors.named_colorscales() 

class AppWithCallbacksAndState:
    def gen_dataframe( self):
        data = [ { 'abstract_template_name': atn, 'concrete_template_name': ctn, **m} for atn, v in self.tagged_bboxes.items() for ctn, (m, _) in v.items()]

        df = pd.DataFrame( data=data)
        df['area'] = df['width']*df['height']
        df['aspect_ratio'] = df['height'] / df['width']

        self.axes = ('width','height')
        #self.axes = ('aspect_ratio','area')

        self.tagged_histos = {}
        for atn, df_group0 in df.groupby(['abstract_template_name']):
            self.tagged_histos[atn] = defaultdict(list)
            for p, df_group1 in df_group0.groupby(list(self.axes)):
                print(atn,p)
                for row_index, row in df_group1.iterrows():
                    print('\t', row['concrete_template_name'])
                    self.tagged_histos[atn][p].append( row['concrete_template_name'])

        df = df[df['abstract_template_name'] == self.module_name]
        df['ordering'] = np.arange(len(df))
        df['size'] = len(df) - np.arange(len(df))

        self.df = df

    def __init__(self, *, tagged_bboxes, module_name):
        self.tagged_bboxes = tagged_bboxes
        self.module_name = module_name

        self.sel = None
        self.md_str = ''

        self.subindex = 0
        self.prev_idx = None

        self.gen_dataframe()
        self.tradeoff = make_tradeoff_fig(self.axes, self.df, log=True)
        self.placement_graph = self.make_placement_graph()

        external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']
        self.app = dash.Dash(__name__, external_stylesheets=external_stylesheets)

        self.app.layout = html.Div(
            id='frame',
            children=[
                html.Div(
                    children=[
                        html.H2(children='Pareto Frontier'),
                        dcc.RadioItems(
                            id='axes-type',
                            options=[{'label': i, 'value': i} for i in ['linear', 'loglog']],
                            value='loglog',
                            labelStyle={'display': 'inline-block'},
                            style={ 'width': '250px', 'display': 'inline-block', 'vertical-align': 'top'}
                        ),
                        dcc.Dropdown(
                            id='colorscale', 
                            options=[{"value": x, "label": x} 
                                     for x in colorscales],
                            value='Blugrn',
                            style={ 'width': '250px', 'display': 'inline-block'}
                        ),
                        dcc.Dropdown(
                            id='module-name', 
                            options=[{"value": x, "label": x} 
                                     for x in self.tagged_bboxes.keys()],
                            value=self.module_name,
                            style={ 'width': '350px'}
                        ),
                        dcc.Graph(
                            id='tradeoff-graph',
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
                            disabled=True,
                            n_clicks=0
                        ),
                        dcc.Graph(
                            id='Placement',
                            figure = self.placement_graph
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
                            Output('tradeoff-graph', 'clickData')),
                      [Input('tradeoff-graph', 'clickData'),
                       Input('tradeoff-graph', 'hoverData'),
                       Input('display-type', 'value')])(self.display_hover_data)

        self.app.callback( (Output('route-current', 'n_clicks'),),
                           [Input('route-current', 'n_clicks')])(self.route_current_placement)

        self.app.callback( (Output('tradeoff-graph', 'figure'),),
                           [Input('colorscale', 'value'),
                            Input('axes-type', 'value'),
                            Input('module-name', 'value')])(self.change_colorscale)

    def make_placement_graph( self, sel=None, *, display_type='All'):
        if display_type == 'All':
            levels = None
            leaves_only = False
        elif display_type == 'Direct':
            levels = 1
            leaves_only = False
        elif display_type == 'Leaves Only':
            leaves_only = True
            levels = None
        else:
            assert False, display_type

        fig = go.Figure()
        title_d = {}

        if sel is not None:
            _, d = self.tagged_bboxes[self.module_name][sel]
            dump_blocks( fig, d, leaves_only, levels)
            title_d = dict(text=sel)

        fig.update_layout(
            autosize=False,
            width=800,
            height=800,
            title=title_d
        )

        max_x = max( m['width']  for _, (m, _) in self.tagged_bboxes[self.module_name].items())
        max_y = max( m['height'] for _, (m, _) in self.tagged_bboxes[self.module_name].items())

        fig.update_xaxes(
            tickvals=[0,max_x],
            range=[0,max(max_x,max_y)]
        )

        fig.update_yaxes(
            tickvals=[0,max_y],
            range=[0,max(max_x,max_y)]
        )

        return fig

    def change_colorscale(self, scale, axes_type, module_name):
        # if module_name changes
        ctx = dash.callback_context
        if ctx.triggered:
            d = ctx.triggered[0]
            if d['prop_id'] == 'module-name.value':
                self.module_name = module_name

        self.gen_dataframe()
        self.tradeoff = make_tradeoff_fig(self.axes, self.df, log=axes_type == 'loglog', scale=scale)
        return (self.tradeoff,)

    def route_current_placement(self, n_clicks):
        if self.sel is not None and n_clicks > 0:
            print( f'Start the router using sel {self.sel}')

        return (0,)

    def display_hover_data(self,clickData,hoverData,display_type):
        display_type_change = False

        ctx = dash.callback_context
        if ctx.triggered:
            d = ctx.triggered[0]
            if d['prop_id'] == 'display-type.value':
                display_type_change = True
                pass
            if d['prop_id'] == 'tradeoff-graph.clickData':
                pass
            if d['prop_id'] == 'tradeoff-graph.hoverData':
                pass

        if clickData is not None:
            [idx, curve_idx, x, y] = [clickData['points'][0][t] for t in ['pointNumber', 'curveNumber', 'x', 'y']]

        if hoverData is not None:
            [idx, curve_idx, x, y] = [hoverData['points'][0][t] for t in ['pointNumber', 'curveNumber', 'x', 'y']]

        if display_type_change:
            self.placement_graph = self.make_placement_graph(self.sel,display_type=display_type)
        elif (clickData is not None or hoverData is not None) and \
             curve_idx == 0:

            lst = self.tagged_histos[self.module_name][(x,y)]

            if self.prev_idx != idx:
                self.subindex = 0
            else:
                self.subindex = (self.subindex+1)%len(lst)
            self.sel = lst[self.subindex]
            self.prev_idx = idx

            self.md_str = f"""```text
Selection: {self.sel}
Coord: {x,y}
Subindex: {self.subindex}/{len(lst)}
```
"""
            self.placement_graph = self.make_placement_graph(self.sel,display_type=display_type)

        return self.placement_graph, self.md_str, None


def run_gui( *, tagged_bboxes, module_name):
    awcas = AppWithCallbacksAndState( tagged_bboxes=tagged_bboxes, module_name=module_name)
    awcas.app.run_server(debug=True,use_reloader=False)
    
    logger.info( f'final module_name: {awcas.module_name} We have access to any state from the GUI object here.')
