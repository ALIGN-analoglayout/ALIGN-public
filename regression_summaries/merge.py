#!/usr/bin/env python

import pandas as pd

df_23 = pd.read_csv( "summary_2021_04_23.csv")
df_25 = pd.read_csv( "summary_2021_04_25.csv")

df_23.merge(df_25, how='outer', on='name').to_csv( 'merged.csv')
