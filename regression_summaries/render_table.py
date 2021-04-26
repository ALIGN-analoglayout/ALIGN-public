#!/usr/bin/env python

import dash
import dash_table
import pandas as pd
import argparse
import re
from collections import defaultdict

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

style_data_conditional = []
for id in df.columns:
    if id == 'name':
        s = { 'if': { 'column_id': id},
              'width': '100px'
        }
        style_data_conditional.append(s)
    if id.endswith('_x') or id.endswith('_y') or id.endswith('_d'):
        s = { 'if': { 'column_id': id},
              'width': '20px',
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

print(style_data_conditional)

app.layout = dash_table.DataTable(
    id='table',
    columns=[{"name": i, "id": i} for i in df.columns],
    data=df.to_dict('records'),
    sort_action='native',
    filter_action='native',
    style_data_conditional=style_data_conditional,
    style_cell={
        'overflow': 'hidden',
        'textOverflow': 'ellipsis',
        'maxWidth': 0
    },
    style_header={
        'overflow': 'hidden',
        'textOverflow': 'ellipsis',
        'maxWidth': 0
    },
    tooltip_data=[
        {
            column: {'value': str(value), 'type': 'markdown'}
            for column, value in row.items()
        } for row in df.to_dict('records')
    ]
)

if __name__ == '__main__':
    app.run_server(debug=True)
