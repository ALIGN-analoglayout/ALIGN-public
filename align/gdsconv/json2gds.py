#! /usr/bin/env python
# -*- coding: utf-8 -*-
"""JSON to GDSII."""

# Basic dependencies:
#   python3
#   python-pip
#   pip install python-gdsii

from __future__ import print_function

import json

from gdsii import tags, types
from gdsii.record import Record
import sys

def unbracket (l):    return str(l)[1:-1]

def quote (s):        return '\"' + s + '\"'

def convert_GDSjson_GDS_fps( ifile, ofile):

    def store_data (tag_name, idata):
        tag = tags.DICT[tag_name]
        tag_type = tags.type_of_tag(tag)
        rest = idata

        if tag_type == types.NODATA:
            data = None
        elif tag_type == types.ASCII:
            data = rest[1:-1].encode() # FIXME
        elif tag_type == types.BITARRAY:
            data = int(rest)
        elif tag_type == types.REAL8:
            data = [float(s) for s in rest.split(',')]
        elif tag_type == types.INT2 or tag_type == types.INT4:
            data = [int(s) for s in rest.split(',')]
        else:
            raise Exception('Unsupported type')
        rec = Record(tag, data)
        rec.save(ofile)

    data = json.load (ifile)
    store_data ('HEADER', str(data['header']))
    for lib in data['bgnlib']:
        store_data ('BGNLIB', unbracket(lib['time']))
        store_data ('LIBNAME', quote(lib['libname']))
        store_data ('UNITS', unbracket(lib['units']))
        for cell in lib['bgnstr']:
            store_data ('BGNSTR', unbracket(cell['time']))
            store_data ('STRNAME', quote(cell['strname']))
            if 'elements' in cell:
                for elem in cell['elements']:
                    t = elem['type']
                    if t == 'boundary':
                        store_data ('BOUNDARY', None)
                        if 'layer' in elem:        store_data ("LAYER", str(elem['layer']))
                        if 'datatype' in elem:     store_data ("DATATYPE", str(elem['datatype']))
                        if 'xy' in elem:           store_data ("XY", unbracket(elem['xy']))
                        if 'propattr' in elem:     store_data ("PROPATTR", str(elem['propattr']))
                        if 'propvalue' in elem:    store_data ("PROPVALUE", quote(elem['propvalue']))
                    elif t == 'path':
                        store_data ('PATH', None)
                        if 'layer' in elem:        store_data ("LAYER", str(elem['layer']))
                        if 'datatype' in elem:     store_data ("DATATYPE", str(elem['datatype']))
                        if 'pathtype' in elem:     store_data ("PATHTYPE", str(elem['pathtype']))
                        if 'width' in elem:        store_data ("WIDTH", str(elem['width']))
                        if 'bgnextn' in elem:      store_data ("BGNEXTN", str(elem['bgnextn']))
                        if 'endextn' in elem:      store_data ("ENDEXTN", str(elem['endextn']))
                        if 'xy' in elem:           store_data ("XY", unbracket(elem['xy']))
                    elif t == 'text':
                        store_data ("TEXT", None)
                        if 'layer' in elem:        store_data ("LAYER", str(elem['layer']))
                        if 'texttype' in elem:     store_data ("TEXTTYPE", str(elem['texttype']))
                        if 'presentation' in elem: store_data ("PRESENTATION", str(elem['presentation']))
                        if 'strans' in elem:       store_data ("STRANS", str(elem['strans']))
                        if 'mag' in elem:          store_data ("MAG", str(elem['mag']))
                        if 'angle' in elem:        store_data ("ANGLE", str(elem['angle']))
                        if 'xy' in elem:           store_data ("XY", unbracket(elem['xy']))
                        if 'string' in elem:       store_data ("STRING", quote(elem['string']))
                    elif t == 'sref':
                        store_data ("SREF", None)
                        if 'sname' in elem:        store_data ("SNAME", quote(elem['sname']))
                        if 'strans' in elem:       store_data ("STRANS", str(elem['strans']))
                        if 'angle' in elem:        store_data ("ANGLE", str(elem['angle']))
                        if 'xy' in elem:           store_data ("XY", unbracket(elem['xy']))
                    store_data ("ENDEL", None)
            store_data ("ENDSTR", None)
        store_data ("ENDLIB", None)

def convert_GDSjson_GDS (name, oname):
    with open (name, 'rt') as ifile, \
         open (oname, 'wb') as ofile:
        convert_GDSjson_GDS_fps( ifile, ofile)

def usage(prog):
    print('Usage: %s <file.json> <file.gds>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        convert_GDSjson_GDS (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)
