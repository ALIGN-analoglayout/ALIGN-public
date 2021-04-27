#!/usr/bin/env python

import dash
from dash.dependencies import Input, Output
import dash_html_components as html
import dash_table
import pandas as pd
import argparse
import re
import webbrowser
from collections import defaultdict
import pathlib
import os

app = dash.Dash(__name__)

def toId( s):
    return s.replace( ' ', '_')

def clean_column_names( df):
    d = {}
    for nm in df.columns.tolist():
        if ' ' in nm:
            d[nm] = toId(nm)
    df.rename( columns=d, inplace=True)

parser = argparse.ArgumentParser( description='Analyze Regression Results and Build CSV Table')
parser.add_argument( '-0', '--csv_input_file0', type=str, help='CSV input file 0 (reference)')
parser.add_argument( '-1', '--csv_input_file1', type=str, help='CSV input file 1 (current)')
parser.add_argument( '-d0', '--regression_directory0', type=str, help='Regression directory 0 (reference)')
parser.add_argument( '-d1', '--regression_directory1', type=str, help='Regression directory 1 (current)')

args = parser.parse_args()

df0 = pd.read_csv( args.csv_input_file0)
df1 = pd.read_csv( args.csv_input_file1)
clean_column_names( df0)
clean_column_names( df1)

df = df0.merge(df1, how='outer', on='name')

p = re.compile( r"^(\S+)_(x|y)$")

names = defaultdict(list)
for nm in df.columns.tolist():
    m = p.match(nm)
    if m:
        names[m.groups()[0]].append( nm)

for k,v in names.items():
    assert set([f'{k}_x', f'{k}_y']) == set(v)

for k,_ in names.items():
    df[f'{k}_d'] = df[f'{k}_y'] - df[f'{k}_x']

df['id'] = df['name']

style_data_conditional = []
for id in df.columns:
    if id == 'name':
        s = { 'if': { 'column_id': id},
              'minWidth': '200px',
              'width': '200px'
        }
        style_data_conditional.append(s)
    if id.endswith('_x') or id.endswith('_y'):
        s = { 'if': { 'column_id': id, 'filter_query': f'{{{id}}} > 0'},
              'color': 'tomato',
              'fontWeight': 'bold'
        }
        style_data_conditional.append(s)
    if id.endswith('_d'):
        s = { 'if': { 'column_id': id, 'filter_query': f'{{{id}}} > 0'},
              'color': 'tomato',
              'fontWeight': 'bold'
        }
        style_data_conditional.append(s)
        s = { 'if': { 'column_id': id, 'filter_query': f'{{{id}}} < 0'},
              'color': 'green',
              'fontWeight': 'bold'
        }
        style_data_conditional.append(s)

app.layout = html.Div([
    dash_table.DataTable(
    id='table',
    columns=[{"name": i, "id": i} for i in df.columns if i != 'id'],
    data=df.to_dict('records'),
    sort_action='native',
    filter_action='native',
    style_data_conditional=style_data_conditional,
    style_cell={
        'height': 'auto',
        'whiteSpace': 'normal',
        'overflow': 'hidden',
        'minWidth': '30px',
        'width': '30px',
        'maxWidth': '30px'
    }
    ),
    html.Div(id='container')
    ])

@app.callback(
    Output('container', 'children'),
    Input('table', 'active_cell')
    )
def update_graphs(active_cell):
    def open_json( active_cell, tag, suffix, regdir):
        if active_cell['column_id'].endswith( tag):
            if regdir:
                print( f'{regdir}')
                nm = active_cell['row_id']
                p = pathlib.Path( regdir) / nm / '3_pnr' / f'{nm}_0.json'
                p0 = pathlib.Path( os.environ['ALIGN_HOME']) / 'Viewer' / 'INPUT'
                if p.is_file() and p0.is_dir():
                    (p0 / f'{nm}_0{suffix}.json').write_text( p.read_text())
                    webbrowser.open( f'http://localhost:8000/?design={nm}_0{suffix}')
    if active_cell:
        open_json( active_cell, '_x', '-0', args.regression_directory0)
        open_json( active_cell, '_y', '-1', args.regression_directory1)
    return ''

if __name__ == '__main__':
    app.run_server(debug=True)
