#! /usr/bin/env python
# -*- coding: utf-8 -*-
"""JSON to TXT."""

# python3
# python-pip
# pip install python-gdsii
from __future__ import print_function

import json
import sys

def quote (s): return '\"' + s + '\"'

def bracket (name):
    return name

def unbracket (name):
    return str(name)[1:-1]

def convert_GDSjson_GDStxt (name, oname):
    ofile = open (oname, 'wt')

    def oprint (*args):
        for i, arg in enumerate(args):
            print (arg, file=ofile, end='')
            if i < len(args) - 1: print (' ', file=ofile, end='')
        print('', file=ofile)
               
    with open (name, 'rt') as a_file:
        data = json.load (a_file)
        oprint ("HEADER:", bracket(data['header']))
        for lib in data['bgnlib']:
            oprint ("BGNLIB:", unbracket(lib['time']))
            oprint ("LIBNAME:", quote(lib['libname']))
            oprint ("UNITS:", unbracket(lib['units']))
            for cell in lib['bgnstr']:
                oprint ("BGNSTR:", unbracket(cell['time']))
                oprint ("STRNAME:", quote(cell['strname']))
                if 'elements' in cell:
                    for elem in cell['elements']:
                        t = elem['type']
                        if t == 'boundary':
                            oprint ("BOUNDARY")
                            if 'layer' in elem: oprint ("LAYER:", bracket(elem['layer']))
                            if 'datatype' in elem: oprint ("DATATYPE:", bracket(elem['datatype']))
                            if 'xy' in elem: oprint ("XY:", unbracket(elem['xy']))
                            if 'propattr' in elem: oprint ("PROPATTR:", bracket(elem['propattr']))
                            if 'propvalue' in elem: oprint ("PROPVALUE:", quote(elem['propvalue']))
                        elif t == 'text':
                            oprint ("TEXT")
                            if 'layer' in elem: oprint ("LAYER:", bracket(elem['layer']))
                            if 'texttype' in elem: oprint ("TEXTTYPE:", bracket(elem['texttype']))
                            if 'presentation' in elem: oprint ("PRESENTATION:", elem['presentation'])
                            if 'strans' in elem: oprint ("STRANS:", elem['strans'])
                            if 'mag' in elem: oprint ("MAG:", bracket(elem['mag']))
                            if 'angle' in elem: oprint ("ANGLE:", bracket(elem['angle']))
                            if 'xy' in elem: oprint ("XY:", unbracket(elem['xy']))
                            if 'string' in elem: oprint ("STRING:", quote(elem['string']))
                        elif t == 'sref':
                            oprint ("SREF")
                            if 'sname' in elem: oprint ("SNAME:", quote(elem['sname']))
                            if 'strans' in elem: oprint ("STRANS:", elem['strans'])
                            if 'angle' in elem: oprint ("ANGLE:", bracket(elem['angle']))
                            if 'xy' in elem: oprint ("XY:", unbracket(elem['xy']))
                        oprint ("ENDEL")
                oprint ("ENDSTR")
            oprint ("ENDLIB")

def usage(prog):
    print('Usage: %s <file.json> %s <file.txt>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        convert_GDSjson_GDStxt (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)

