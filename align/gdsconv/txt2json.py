#! /usr/bin/env python
# -*- coding: utf-8 -*-
"""TXT to JSON."""

from gdsii import tags, types
import json
import sys
import re

def print_data (tag_type, data): 
    if tag_type == types.ASCII:        return "%s" % data[1:-1]
    elif tag_type == types.BITARRAY:   return int(data)
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
    
def isElement (e):
    return e == "BOUNDARY" or e == "PATH" or e == "SREF" or \
           e == "AREF" or e == "TEXT" or e == "NODE" or e == "BOX"
    
def convert_GDStxt_GDSjson (name, oname):
    level = 0
    rexp = re.compile(r'^(?P<tag>[^:]+)(:\s*(?P<rest>.*))?$')
    ofile = open (oname, 'wt')

    top = {}
    cursors = [top, {}, {}, {}, {}, {}, {}]
        
    lineno = 0
    with open (name, 'rt') as ifile:
        for line in ifile:
            lineno += 1
            m = rexp.match (line.strip())
            if not m:
                print('Parse error at line {0}'.format(lineno), file=sys.stderr)
                sys.exit(1)
            tag_name = m.group('tag')
            rest = m.group('rest')

            tag = tags.DICT[tag_name]
            tag_type = tags.type_of_tag(tag)

            jsonName = ""
            if isElement (tag_name):          jsonName = "elements"
            else:                             jsonName = tag_name.lower()

            if ((tag_type != types.NODATA and tag_name[0:3] == "BGN") or
                    isElement(tag_name)):
                if isinstance(cursors[level], dict):
                    level = level + 1
                    cursors[level] = []
                    cursors[level - 1][jsonName] = cursors[level]
                level = level + 1
                cursors[level] = {}
                cursors[level - 1].append (cursors[level])

                if isElement(tag_name): cursors[level]["type"] = tag_name.lower()
                if tag_name[0:3] == "BGN": cursors[level]["time"] = print_data(tag_type, rest)

            if tag_type != types.NODATA and tag_name[0:3] != "BGN":
                cursors[level][jsonName] = print_data(tag_type, rest)
            elif tag_name[0:3] == "END":
                if isinstance(cursors[level - 1], dict): level = level - 1
                level = level - 1

    json.dump (top, ofile, indent=4)

def usage(prog):
    print('Usage: %s <file.txt> <file.json>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        convert_GDStxt_GDSjson (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)
