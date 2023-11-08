#! /usr/bin/env python
# -*- coding: utf-8 -*-
"""GDSII to JSON."""

#  This helps understand:  http://www.buchanan1.net/stream_description.html
#  element:  boundary | path | sref | aref | text | node | box

from gdsii import types
from gdsii.record import Record
import json
import sys

def show_data(rec):
    """Shows data in a human-readable format."""
    data = rec.data
    tag_type = rec.tag_type
    if tag_type == types.ASCII:        return "%s" % data.decode()
    elif tag_type == types.BITARRAY:   return int(data)
    elif tag_type == types.REAL8:
        if len(data) > 1:              return [float(s) for s in data]
        else:                          return data[0]
    elif tag_type == types.INT2 or tag_type == types.INT4:
        if len(data) > 1:              return [int(s) for s in data]
        else:                          return data[0]
    return '\"' + ', '.join('{0}'.format(i) for i in data) + '\"'

def isElement (e):
    return e == "BOUNDARY" or e == "PATH" or e == "SREF" or \
           e == "AREF" or e == "TEXT" or e == "NODE" or e == "BOX"

def convert_GDS_GDSjson (name, oname):
    level = 0

    ofile = open (oname, 'wt')

    top = {}
    cursors = [top, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}]

    with open(name, 'rb') as a_file:
        for rec in Record.iterate(a_file):
            tag_name = rec.tag_name
            tag_type = rec.tag_type

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
                if tag_name[0:3] == "BGN": cursors[level]["time"] = show_data (rec)

            if tag_type != types.NODATA and tag_name[0:3] != "BGN":
                cursors[level][jsonName] = show_data (rec)
            elif tag_name[0:3] == "END":
                if isinstance(cursors[level - 1], dict): level = level - 1
                level = level - 1


    json.dump (top, ofile, indent=4)

def usage(prog):
    print('Usage: %s <file.gds> <file.json>' % prog)

if __name__ == '__main__':
    if (len(sys.argv) == 3):
        convert_GDS_GDSjson (sys.argv[1], sys.argv[2])
    else:
        usage(sys.argv[0])
        sys.exit(1)
    sys.exit(0)
