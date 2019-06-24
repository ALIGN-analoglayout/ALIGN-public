import copy
import collections
import json

from . import canvas

import os
import os.path

import pathlib

def gen( c, dirname):
    pathlib.Path(dirname).mkdir( parents=True, exist_ok=True)
    
    for (k,v) in c.generators.items():
        print( k, v)

    return True

