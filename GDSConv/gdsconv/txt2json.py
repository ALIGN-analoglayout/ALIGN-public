#! /usr/bin/python
# -*- coding: utf-8 -*-
"""TXT to JSON."""

from __future__ import print_function
from gdsii import tags, types
from gdsii.record import Record
import sys
import re

def show_data(tag_type, data):
    """Shows data in a human-readable format."""
    if tag_type == types.ASCII:
        return '"%s"' % data[1:-1].encode() # TODO escape
    elif tag_type == types.BITARRAY:
        return int(data)
    elif tag_type == types.REAL8:
        if len(data.split(',')) > 1:
            return [float(s) for s in data.split(',')]
        else:
            return float(data)
    elif tag_type == types.INT2 or tag_type == types.INT4:
        if len(data.split(',')) > 1:
            return [int(s) for s in data.split(',')]
        else:
            return int(data)
    else:
        raise Exception ('Unsupported type')
    
    return '\"' + ', '.join('{0}'.format(i) for i in data) + '\"'

def quote (s): return '\"' + s + '\"'

def isElement (e):
    return e == "BOUNDARY" or e == "PATH" or e == "SREF" or e == "AREF" or e == "TEXT" or e == "NODE" or e == "BOX"
    
def convert_GDStxt_GDSjson (name, oname):
    level = 0
    first = True
    levelTag = [""] * 256
    rexp = re.compile(r'^(?P<tag>[^:]+)(:\s*(?P<rest>.*))?$')
    lineno = 1
    ofile = open (oname, 'wb')

    def indent (l):
        while l > 0:
            print("    ", end='', file=ofile)
            l = l - 1
            
    def indentPrint (level, first, *s):
        if not first:        print (',', file=ofile)
        else:                print ('', file=ofile)
        indent(level)
        for i in s:          print (i, end='', file=ofile)
        
    with open (name, 'rb') as ifile:
        indentPrint(level, first, '{')
        for line in ifile:
            stripped = line.strip()
            m = rexp.match(stripped)
            if not m:
                print('Parse error at line {0}'.format(lineno), file=sys.stderr)
                sys.exit(1)
            tag_name = m.group('tag')
            rest = m.group('rest')

            tag = tags.DICT[tag_name]

            tag_type = tags.type_of_tag(tag)

            if tag_type == types.NODATA:
                if isElement(tag_name):
                    if levelTag[level] == "":
                        indentPrint (level, first, quote("elements"), ": [")
                        level = level + 1
                        levelTag[level] = tag_name
                        first = True
                    indentPrint (level, first, "{")
                    level = level + 1
                    first = True
                    indentPrint (level, first, quote("type"), ": ", quote(tag_name.lower()))
                    first = False
                elif tag_name == "ENDEL" or tag_name == "ENDSTR" or tag_name == "ENDLIB":
                    if levelTag[level] != "":
                        s = levelTag[level]
                        levelTag[level] = ""
                        level = level - 1
                        indentPrint (level, True, ']')
                        first = False
                        level = level - 1
                        if tag_name != s:
                            indentPrint (level, True, '}')
                            first = False
                    else:
                        level = level - 1
                        indentPrint (level, True, '}')
                        first = False
                else:
                    print("ERROR: unrecognized tag:", tag_name)
            else:
                if tag_name == "BGNLIB" or tag_name == "BGNSTR":
                    if levelTag[level] == "":
                        indentPrint (level, first, quote(tag_name.lower()), ": [")
                        level = level + 1
                        levelTag[level] = tag_name
                        first = True
                    indentPrint (level, first, "{")
                    level = level + 1
                    first = True
                    indentPrint (level, first, quote('time'), ": ", show_data(tag_type, rest))
                else:
                    indentPrint (level, first, quote(tag_name.lower()), ": ", show_data(tag_type, rest))
                first = False
        if levelTag[level] != "":
            levelTag[level] = ""
            level = level - 1
            indentPrint(level, True, ']')
        indentPrint(level, True, '}')

def usage(prog):
    print('Usage: %s <file.txt> <file.json>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        convert_GDStxt_GDSjson (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)
