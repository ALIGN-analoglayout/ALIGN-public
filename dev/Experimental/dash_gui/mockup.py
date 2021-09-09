# Run this app with `python mockup.py` and
# visit http://127.0.0.1:8050/ in your web browser.

import dash
from dash import html
from dash.dependencies import Input, Output
import dash_html_components as html

import itertools
import random

from polish import *

from collections import defaultdict

import logging
logging.basicConfig(level=logging.INFO)

import argparse



class AppWithCallbacksAndState:
    def __init__(self, placements, histo, pairs, max_x, max_y):
        external_stylesheets = ['https://codepen.io/chriddyp/pen/bWLwgP.css']
        self.app = dash.Dash(__name__, external_stylesheets=external_stylesheets)

        self.placements = placements
        self.histo = histo
        self.pairs = pairs
        self.max_x = max_x
        self.max_y = max_y

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
                            figure = make_placement_graph([], self.max_x, self.max_y)
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


    def display_hover_data(self,clickData):
        placement = []
        md_str = ''
        if clickData is not None:
            points = clickData['points']
            assert 1 == len(points)
            idx = points[0]['pointNumber']

            lst = self.histo[self.pairs[idx]]

            if self.prev_idx != idx:
                self.subindex = 0
            else:
                self.subindex = (self.subindex+1)%len(lst)
            ps = lst[self.subindex]
            self.prev_idx = idx

            md_str = f"""```text
{polish2tree(ps)}

Polish: {ps}
Coord: {self.pairs[idx]}
Subindex: {self.subindex}/{len(lst)}
```

"""
            placement = self.placements[self.histo[self.pairs[idx]][self.subindex]]

        return make_placement_graph(placement, self.max_x, self.max_y), md_str, None

def run_gui( DB, bboxes):
    logging.info( f'Running GUI: {bboxes}')

    histo = defaultdict(list)
    for idx,p in enumerate(bboxes):
        histo[p].append(idx)

    pairs = list(histo.keys())

    max_x = max( p[0] for p in pairs)
    max_y = max( p[1] for p in pairs)

    logging.info( f'histo: {histo}')

    awcas = AppWithCallbacksAndState( [], histo, pairs, max_x, max_y)
    awcas.app.run_server(debug=False)


if __name__ == '__main__':

    parser = argparse.ArgumentParser( description='Mockup of ALIGN UI')
    parser.add_argument( '-s', '--block_str', type=str, default='ABCD', help='Blocks to use in enumeration; must only include the characters "ABCEDF"; strings longer than 5 will take a long time')

    args = parser.parse_args()

    AppWithCallbacksAndState( *main(args.block_str)).app.run_server(debug=True)
