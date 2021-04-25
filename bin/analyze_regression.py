#!/usr/bin/env python

import pathlib
import pandas as pd
import re
import argparse
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
                assert False, line
                counts['other'] += 1

    return counts


def collect_errors( regression_path):

    df = pd.DataFrame(columns=('name', 'failed before pnr', 'failed during pnr') + tuple(p[0] for p in patterns) + ('other',))

    for path in regression_path.iterdir():
        pnr = path / '3_pnr'
        if pnr.is_dir():
            errors_path = pnr / f'{path}_0.errors'
            if errors_path.is_file():
                counts = parse_errors(errors_path)
                d = {
                    'name': str(path),
                    'failed before pnr': False,
                    'failed during pnr': False
                }
                for k, v in counts.items():
                    d[k] = v
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
    with open( args.csv_output_file, "wt") as fp:
        df.to_csv( fp, header=True, index=False)
