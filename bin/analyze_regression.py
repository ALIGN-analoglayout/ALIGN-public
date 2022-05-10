#!/usr/bin/env python

import pathlib
import pandas as pd
import re
import argparse
import json
from collections import defaultdict

patterns = [
    ('open', re.compile( r'^OPEN .*$')),
    ('short', re.compile( r'^SHORT .*$')),
    ('minlen', re.compile( r'^DRC ERROR MinLength violation .*$')),
    ('terminal', re.compile( r'^DRC ERROR Terminal .*$'))
]


def parse_errors( errors_path):
    counts = { p[0] : 0 for p in patterns}
    counts['other'] = 0
    
    with errors_path.open( 'rt') as fp:
        for line in fp:
            line = line.rstrip('\n')
            match = False
            for k, p in patterns:
                m = p.match( line)
                if m:
                    counts[k] += 1
                    match = True
            if not match:
                print( f'Mapping error to other: {line}')
                counts['other'] += 1

    return counts

def get_area( json_path):
    with json_path.open( 'rt') as fp:
        j = json.load( fp)
    r = j['bbox']
    w, h = (r[2]-r[0])/10000, (r[3]-r[1])/10000
    aspect = max( h/w, w/h)
    return w, h, w*h, aspect

def collect_errors( regression_path):
    """Apparently the append method in pd.DataFrame has been deprecated; we should do this another way
"""

    df = pd.DataFrame(columns=('name', 'failed before pnr', 'failed during pnr') + tuple(p[0] for p in patterns) + ('other', 'w', 'h', 'area', 'aspect'))

    for path in regression_path.iterdir():
        if not path.is_dir():
            continue
        pnr = path / '3_pnr'
        if pnr.is_dir():
            errors_path = pnr / f'{str(path).upper()}_0.errors'
            if errors_path.is_file():
                counts = parse_errors(errors_path)
                d = {
                    'name': str(path),
                    'failed before pnr': False,
                    'failed during pnr': False
                }
                for k, v in counts.items():
                    d[k] = v

                json_path = pnr / f'{str(path).upper()}_0.json'

                if json_path.is_file():
                    w, h, area, aspect = get_area( json_path)
                    d['h'] = h
                    d['w'] = w
                    d['area'] = area
                    d['aspect'] = aspect

                df = df.append( d, ignore_index=True)
            else:
                df = df.append( {
                    'name': str(path),
                    'failed before pnr': False,
                    'failed during pnr': True
                }, ignore_index=True)

        else:
            df = df.append( {
                'name': str(path),
                'failed before pnr': True
            }, ignore_index=True)

    return df

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description='Analyze Regression Results and Build CSV Table')
    parser.add_argument( '-d', '--regression_directory', type=str, default='.', help='Location of regression results, typically $ALIGN_WORK_DIR/FinFET14nm_Mock_PDK')
    parser.add_argument( '-o', '--csv_output_file', type=str, default='summary.csv', help='Output csv file name')

    args = parser.parse_args()

    df = collect_errors( pathlib.Path(args.regression_directory))

    df.to_csv( args.csv_output_file, header=True, index=False)
