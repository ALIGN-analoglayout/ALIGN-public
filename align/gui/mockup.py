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

def define_axes( fig, log, max_x, max_y):
    if log:
        fig.update_xaxes(
            type="log"
        )
        fig.update_yaxes(
            type="log"
        )
    else:
        fig.update_xaxes(
            range=[0,max_x*1.1]
        )
        fig.update_yaxes(
            range=[0,max_y*1.1]
        )


def define_colorscale( fig, col):
    min_c,max_c = col.min(),col.max()
    if min_c == max_c: max_c = min_c + 0.1
    fig.update_coloraxes(
        cmin=min_c,
        cmax=max_c,
        reversescale=True
    )

def make_tradeoff_fig_ha(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="hpwl",
        y="area",
        color="constraint_penalty",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['width','height']
    )

    best_x = df['hpwl'].values[0]
    best_y = df['area'].values[0]

    min_x, max_x = min(df['hpwl']),max(df['hpwl'])
    min_y, max_y = min(df['area']),max(df['area'])

    sweep_x = np.linspace( min_x, max_x, 101)
    sweep_y = best_y*(2 - sweep_x/best_x)

    fig.add_trace(
        go.Scatter( 
            x=sweep_x,
            y=sweep_y,
            mode='lines',
            showlegend=False
        )
    )

    define_colorscale( fig, df['constraint_penalty'])
    define_axes( fig, log, max_x, max_y)

    return fig

def make_tradeoff_fig_nn(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="hpwl_norm",
        y="area_norm",
        color="constraint_penalty",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['width','height']
    )

    best_x = df['hpwl_norm'].values[0]
    best_y = df['area_norm'].values[0]

    min_x, max_x = min(df['hpwl_norm']),max(df['hpwl_norm'])
    min_y, max_y = min(df['area_norm']),max(df['area_norm'])

    sweep_x = np.linspace( min_x, max_x, 101)
    sweep_y = best_y*(2 - sweep_x/best_x)

    fig.add_trace(
        go.Scatter( 
            x=sweep_x,
            y=sweep_y,
            mode='lines',
            showlegend=False
        )
    )

    define_colorscale( fig, df['constraint_penalty'])
    define_axes( fig, log, max_x, max_y)

    return fig

def make_tradeoff_fig_ac(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="area",
        y="cost",
        color="constraint_penalty",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['width','height']
    )

    y = df['cost'].min()

    min_x, max_x = min(df['area']),max(df['area'])
    min_y, max_y = min(df['cost']),max(df['cost'])

    sweep_x = np.linspace( min_x, max_x, 101)
    sweep_y = y+0*sweep_x

    fig.add_trace(
        go.Scatter( 
            x=sweep_x,
            y=sweep_y,
            mode='lines',
            showlegend=False
        )
    )

    define_colorscale( fig, df['constraint_penalty'])
    define_axes( fig, log, max_x, max_y)

    return fig




def make_tradeoff_fig_hc(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="hpwl",
        y="cost",
        color="constraint_penalty",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['width','height']
    )

    y = df['cost'].min()

    min_x, max_x = min(df['hpwl']),max(df['hpwl'])
    min_y, max_y = min(df['cost']),max(df['cost'])

    sweep_x = np.linspace( min_x, max_x, 101)
    sweep_y = y+0*sweep_x

    fig.add_trace(
        go.Scatter( 
            x=sweep_x,
            y=sweep_y,
            mode='lines',
            showlegend=False
        )
    )

    define_colorscale( fig, df['constraint_penalty'])
    define_axes( fig, log, max_x, max_y)

    return fig

def make_tradeoff_fig_ss(df, log=False, scale='Blugrn'):
    fig = px.scatter(
        df,
        x="hpwl_scale",
        y="area_scale",
        color="constraint_penalty",
        color_continuous_scale=scale,
        size="size",
        width=800,
        height=800,
        hover_name="concrete_template_name",
        hover_data=['width','height']
    )

    min_x, max_x = min(df['hpwl_norm']),max(df['hpwl_norm'])
    min_y, max_y = min(df['area_norm']),max(df['area_norm'])

    define_colorscale( fig, df['constraint_penalty'])
    define_axes( fig, log, max_x, max_y)

    return fig

def make_tradeoff_fig( axes, df, log=False, scale='Blugrn'):
    if   axes == ('width', 'height'):
        return make_tradeoff_fig_wh( df, log, scale)
    elif axes == ('aspect_ratio', 'area'):
        return make_tradeoff_fig_aa( df, log, scale)
    elif axes == ('hpwl', 'area'):
        return make_tradeoff_fig_ha( df, log, scale)
    elif axes == ('area', 'cost'):
        return make_tradeoff_fig_ac( df, log, scale)
    elif axes == ('hpwl', 'cost'):
        return make_tradeoff_fig_hc( df, log, scale)
    elif axes == ('hpwl_scale', 'area_scale'):
        return make_tradeoff_fig_ss( df, log, scale)
    elif axes == ('hpwl_norm', 'area_norm'):
        return make_tradeoff_fig_nn( df, log, scale)
    else:
        assert False, axes

colorscales = ['Blugrn'] + px.colors.named_colorscales() 

class AppWithCallbacksAndState:
    def gen_dataframe( self):
        data = [ { 'abstract_template_name': atn, 'concrete_template_name': ctn, **m} for atn, v in self.tagged_bboxes.items() for ctn, (m, _) in v.items()]

        df = pd.DataFrame( data=data)
        df['area'] = df['width']*df['height']
        df['aspect_ratio'] = df['height'] / df['width']

        self.tagged_histos = {}
        for atn, df_group0 in df.groupby(['abstract_template_name']):
            self.tagged_histos[atn] = defaultdict(list)
            for p, df_group1 in df_group0.groupby(list(self.axes)):
                for row_index, row in df_group1.iterrows():
                    self.tagged_histos[atn][p].append( row['concrete_template_name'])

        df = df[df['abstract_template_name'] == self.module_name]
        df['ordering'] = np.arange(len(df))
        df['size'] = len(df) - np.arange(len(df))

        self.df = df

    def __init__(self, *, tagged_bboxes, module_name):
        self.tagged_bboxes = tagged_bboxes
        self.module_name = module_name

        self.sel = None
        self.title = None

        self.subindex = 0
        self.prev_idx = None

        self.axes = ('hpwl', 'area')

        self.gen_dataframe()
        self.tradeoff = make_tradeoff_fig(self.axes, self.df, log=False)
        self.placement_graph = self.make_placement_graph()

        self.app = dash.Dash(__name__, assets_ignore=r'.*\.#.*')

        self.app.layout = html.Div(
            id='frame',
            children=[
                html.Div(
                    id='pareto-col',
                    children=[
                        html.H2(children='Pareto Frontier'),
                        dcc.RadioItems(
                            id='axes-type',
                            options=[{'label': i, 'value': i} for i in ['linear', 'loglog']],
                            value='linear'
                        ),
                        dcc.Dropdown(
                            id='tradeoff-type', 
                            options=[{"value": x, "label": x} 
                                     for x in ['width-height', 'aspect_ratio-area', 'hpwl-area', 'area-cost', 'hpwl-cost', 'hpwl_scale-area_scale', 'hpwl_norm-area_norm']],
                            value='hpwl-area'
                        ),
                        dcc.Dropdown(
                            id='colorscale', 
                            options=[{"value": x, "label": x} 
                                     for x in colorscales],
                            value='Blugrn'
                        ),
                        dcc.Dropdown(
                            id='module-name', 
                            options=[{"value": x, "label": x} 
                                     for x in self.tagged_bboxes.keys()],
                            value=self.module_name
                        ),
                        dcc.Graph(
                            id='tradeoff-graph',
                            figure=self.tradeoff
                        )
                    ]
                ),
                html.Div(
                    id='placement-col',
                    children=[    
                        html.H2(children='Placement'),
                        dcc.RadioItems(
                            id='display-type',
                            options=[{'label': i, 'value': i} for i in ['All', 'Direct', 'Leaves Only']],
                            value='All'
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
                    ]
                ),
                html.Div(
                    id='tree-col',
                    children=[    
                        html.Img(src=self.app.get_asset_url('align.png'))
                    ]
                )
            ]
        )

        self.app.callback( (Output('Placement', 'figure'),
                            Output('tradeoff-graph', 'clickData')),
                      [Input('tradeoff-graph', 'clickData'),
                       Input('tradeoff-graph', 'hoverData'),
                       Input('display-type', 'value')])(self.display_hover_data)

        self.app.callback( (Output('route-current', 'n_clicks'),),
                           [Input('route-current', 'n_clicks')])(self.route_current_placement)

        self.app.callback( (Output('tradeoff-graph', 'figure'),),
                           [Input('colorscale', 'value'),
                            Input('tradeoff-type', 'value'),
                            Input('axes-type', 'value'),
                            Input('module-name', 'value')])(self.change_colorscale)

    def make_placement_graph( self, *, display_type='All'):
        sel = self.sel
        title = self.title

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
            title_d = dict(text=sel if title is None else title)

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

    def change_colorscale(self, scale, tradeoff_type, axes_type, module_name):
        # if module_name changes
        ctx = dash.callback_context
        if ctx.triggered:
            d = ctx.triggered[0]
            if d['prop_id'] == 'module-name.value':
                self.module_name = module_name
            elif d['prop_id'] == 'tradeoff-type.value':
                self.axes = tuple(tradeoff_type.split('-'))

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
            self.placement_graph = self.make_placement_graph(display_type=display_type)
        elif (clickData is not None or hoverData is not None) and \
             curve_idx == 0:

            lst = self.tagged_histos[self.module_name][(x,y)]

            if self.prev_idx != idx:
                self.subindex = 0
            else:
                self.subindex = (self.subindex+1)%len(lst)
            self.sel = lst[self.subindex]
            self.prev_idx = idx

            self.title = f'{self.sel} {self.subindex}/{len(lst)}'

            self.placement_graph = self.make_placement_graph(display_type=display_type)

        return self.placement_graph, None


def run_gui( *, tagged_bboxes, module_name):
    awcas = AppWithCallbacksAndState( tagged_bboxes=tagged_bboxes, module_name=module_name)
    awcas.app.run_server(debug=True,use_reloader=False)
    
    logger.info( f'final module_name: {awcas.module_name} We have access to any state from the GUI object here.')
