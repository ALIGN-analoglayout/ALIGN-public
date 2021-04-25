#!/usr/bin/env python

import argparse
import pandas as pd

if __name__ == "__main__":
    parser = argparse.ArgumentParser( description='Analyze Regression Results and Build CSV Table')
    parser.add_argument( '-0', '--csv_input_file0', type=str, help='CSV input file 0 (reference)')
    parser.add_argument( '-1', '--csv_input_file1', type=str, help='CSV input file 1 (current)')
    parser.add_argument( '-o', '--csv_output_file', type=str, default='merged.csv', help='CSV output file')

    args = parser.parse_args()

    df0 = pd.read_csv( args.csv_input_file0)
    df1 = pd.read_csv( args.csv_input_file1)

    df0.merge(df1, how='outer', on='name').to_csv( args.csv_output_file, index=False)
