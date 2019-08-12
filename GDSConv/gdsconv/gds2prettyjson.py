#! /usr/bin/env python
# -*- coding: utf-8 -*-
"""GDSII to PRETTY JSON."""
                        
#  This helps understand:  http://www.buchanan1.net/stream_description.html
#  element:  boundary | path | sref | aref | text | node | box

from __future__ import print_function
from gdsii import types
from gdsii.record import Record
import sys

def show_data(rec):
    """Shows data in a human-readable format."""
    data = rec.data
    tag_type = rec.tag_type
    if tag_type == types.ASCII:        return '"%s"' % data.decode() # TODO escape
    elif tag_type == types.BITARRAY:   return str(data)
    elif tag_type == types.REAL8:
        if len(data) > 1:              return [float(s) for s in data]
        else:                          return data[0]
    elif tag_type == types.INT2 or tag_type == types.INT4:
        if len(data) > 1:              return [int(s) for s in data]
        else:                          return data[0]
    return '\"' + ', '.join('{0}'.format(i) for i in data) + '\"'

def quote (s): return '\"' + s + '\"'

def isElement (e):
    return e == "BOUNDARY" or e == "PATH" or e == "SREF" or e == "AREF" or e == "TEXT" or e == "NODE" or e == "BOX"

def convert_GDS_GDSprettyjson (name, oname):
    level = 0

    ofile = open (oname, 'wt')
    def indent (l):
        while l > 0:
            print("    ", end='', file=ofile)
            l = l - 1

    def indentPrint (first, *s):
        if not first:        print (',', file=ofile)
        else:                print ('', file=ofile)
        indent(level)
        for i in s:          print (i, end='', file=ofile)
        
    first = True
    levelTag = [""] * 256
    with open(name, 'rb') as a_file:
        indentPrint (first, '{')
        for rec in Record.iterate(a_file):
            if rec.tag_type == types.NODATA:
                if isElement(rec.tag_name):
                    if levelTag[level] == "":
                        indentPrint (first, quote("elements"), ": [")
                        level = level + 1
                        levelTag[level] = rec.tag_name
                        first = True
                    indentPrint (first, "{")
                    level = level + 1
                    indentPrint (True, quote("type"), ": ", quote(rec.tag_name.lower()))
                elif rec.tag_name == "ENDEL" or rec.tag_name == "ENDSTR" or rec.tag_name == "ENDLIB":
                    if levelTag[level] != "":
                        s = levelTag[level]
                        levelTag[level] = ""
                        level = level - 1
                        indentPrint (True, ']')
                        level = level - 1
                        if rec.tag_name != s:
                            indentPrint (True, '}')
                    else:
                        level = level - 1
                        indentPrint (True, '}')
                else:
                    print('>', rec.tag_name)
            else:
                if rec.tag_name == "BGNLIB" or rec.tag_name == "BGNSTR":
                    if levelTag[level] == "":
                        indentPrint (first, quote(rec.tag_name.lower()), ": [")
                        level = level + 1
                        levelTag[level] = rec.tag_name
                        first = True
                    indentPrint (first, "{")
                    level = level + 1
                    indentPrint (True, quote('time'), ": ", show_data(rec))
                else:
                    indentPrint (first, quote(rec.tag_name.lower()), ": ", show_data(rec))
            first = False
        if levelTag[level] != "":
            levelTag[level] = ""
            level = level - 1
            indentPrint (True, ']')
        indentPrint (True, '}')

def usage(prog):
    print('Usage: %s <file.gds> <file.json>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        convert_GDS_GDSprettyjson (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)
