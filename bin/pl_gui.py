#!/usr/bin/env python
import numpy
import gdspy
import json
import argparse
import os
import PySimpleGUI as sg

ap = argparse.ArgumentParser()
ap.add_argument( "-p", "--pl_file", type=str, default="", help='<filename.placement_verilog.json>')
ap.add_argument( "-t", "--top_cell", type=str, default="", help='<top cell>')
args = ap.parse_args()
print(f"placement verilog : {args.pl_file}")
print(f"top cell          : {args.top_cell}")

if args.pl_file == "" or args.top_cell == "":
    ap.print_help()
    exit()

class Transform:
    def __init__(self, oX = 0, oY = 0, sX = 1, sY = 1):
        self._oX = oX 
        self._oY = oY
        self._sX = sX
        self._sY = sY
    def __str__(self):
        return f'({str(self._oX)} {str(self._oY)} {str(self._sX)} {str(self._sY)})'

class Instance:
    def __init__(self, name = "", tr = Transform(), modu = None):
        self._name = name
        self._tr   = tr
        self._modu = modu
    def __str__(self):
        return f'{self._name} {str(self._tr)}'

class Module:
    def __init__(self, name = "", leaf = False):
        self._name      = name
        self._instances = dict()
        self._added     = False
        self._leaf      = leaf
        self._fname     = ""
        self._cell      = None
        self._bbox      = None
        self._width     = 0
        self._height    = 0
    def __str__(self):
        s = f"{self._name} '{self._fname}' {self._cell}"
        for i in self._instances:
            s += f' [{str(i)} {i._modu._name}]'
        return s

modules = dict()
if args.pl_file:
    with open(args.pl_file) as fp:
        pldata = json.load(fp)
        for l in pldata.get("leaves"):
            lname = l.get("concrete_name")
            if lname:
                modu = Module(lname, True)
                modu._bbox = l.get("bbox")
                modu._width = modu._bbox[2] - modu._bbox[0]
                modu._height = modu._bbox[3] - modu._bbox[1]
                modules[modu._name] = modu
        for m in pldata.get("modules"):
            mname = m.get("concrete_name")
            if mname:
                modu = Module(mname)
                modu._bbox = m.get("bbox")
                modu._width = modu._bbox[2] - modu._bbox[0]
                modu._height = modu._bbox[3] - modu._bbox[1]
                for i in m.get("instances"):
                    iname = i.get("concrete_template_name")
                    trstr = i.get("transformation")
                    tr = Transform()
                    if trstr:
                        tr._oX, tr._oY = trstr["oX"], trstr["oY"]
                        tr._sX, tr._sY = trstr["sX"], trstr["sY"]
                    if iname:
                        modu._instances[i.get("instance_name")] = Instance(iname, tr)
                modules[modu._name] = modu

for mname in modules:
    m = modules[mname]
    for iname in m._instances:
        inst = m._instances[iname]
        if not inst._modu:
            inst._modu = modules[inst._name]
            inst._width = inst._modu._width
            inst._height = inst._modu._height
            if inst._tr._sX < 0:
                inst._tr._oX -= inst._width
            if inst._tr._sY < 0:
                inst._tr._oY -= inst._height
rect_name = dict()
rect_handl = dict()


if args.top_cell not in modules:
    print(f'{args.top_cell} not found in {args.pl_file}')
    exit()


CSIZE = 800

oper = list()
def main():

    sg.theme('Dark Blue 3')

    col = [
      [sg.Button('Undo', key='-UNDO-', size=(4,1))],
      [sg.Button('Legalize', key='-LGL-')]
    ]

    layout = [[sg.Graph(
        canvas_size=(CSIZE, CSIZE),
        graph_bottom_left=(0, 0),
        graph_top_right=(CSIZE, CSIZE),
        key="-GRAPH-",
        change_submits=True,  # mouse click events
        background_color='lightblue',
        drag_submits=True), sg.Col(col) ],
        [sg.Text(key='info', size=(20, 1))]]

    window = sg.Window("Draw and move cells", layout, finalize=True, resizable = True, border_depth=5)
    graph = window["-GRAPH-"] 

    topm = modules[args.top_cell]
    maxdim = max(topm._width, topm._height) * 1.2
    for iname in topm._instances:
        inst = modules[args.top_cell]._instances[iname]
        x = inst._tr._oX * CSIZE / maxdim
        y = inst._tr._oY * CSIZE / maxdim
        w = inst._modu._width * CSIZE / maxdim
        h = inst._modu._height * CSIZE / maxdim
        rect = graph.draw_rectangle((x, y), (x + w, y + h), fill_color='#DEDEDE', line_color='red')
        rect_name[rect] = iname
        rect_handl[rect] = graph.draw_text(rect_name[rect], (x + w/2, y + h/2), color = "black", font = None, angle = 0, text_location = "center")


    dragging = False
    start_point = end_point = prior_rect = None
    graph.bind('<Button-3>', '+RIGHT+')
    while True:
        event, values = window.read()
        if event is None:
            break  # exit
        if event is '-UNDO-':
            if oper:
                op = oper.pop()
                if op:
                    graph.move_figure(op[0], -op[1], -op[2])
                    graph.move_figure(rect_handl[op[0]], -op[1], -op[2])
         #elif event is '-MOVE-':
          #   graph.Widget.config(cursor='fleur')
        elif not event.startswith('-GRAPH-'):
            graph.Widget.config(cursor='left_ptr')

        if event == "-GRAPH-":
            x, y = values["-GRAPH-"]
            if not dragging:
                start_point = (x, y)
                dragging = True
                drag_figures = graph.get_figures_at_location((x,y))
                lastxy = x, y
            else:
                end_point = (x, y)
            if prior_rect:
                graph.delete_figure(prior_rect)
            delta_x, delta_y = x - lastxy[0], y - lastxy[1]
            lastxy = x,y
            if None not in (start_point, end_point):
               for fig in drag_figures:
                   if fig not in rect_handl:
                       continue
                   graph.move_figure(fig, delta_x, delta_y)
                   x = rect_handl[fig] if fig in rect_handl else None
                   if x:
                       graph.move_figure(x, delta_x, delta_y)
                   if oper and (oper[-1][0] == fig):
                       oper[-1][1] += delta_x
                       oper[-1][2] += delta_y
                   else:
                       oper.append([fig, delta_x, delta_y])
                   graph.update()
        elif event.endswith('+UP'):
            info = window["info"]
            info.update(value=f"{prior_rect} grabbed rectangle from {start_point} to {end_point}")
            if start_point and end_point and prior_rect:
                if prior_rect not in rect_name:
                    rect_name[prior_rect] = "rect_" + str(len(rect_name))
                    rect_handl[prior_rect] = graph.draw_text(rect_name[prior_rect], ((start_point[0] + end_point[0])/2, (start_point[1] + end_point[1])/2), color = "black", font = None, angle = 0, text_location = "center")
                else:
                    graph.relocate_figure(rect_handl[prior_rect], (start_point[0] + end_point[0])/2, (start_point[1] + end_point[1])/2)
            start_point, end_point = None, None  # enable grabbing a new rect
            dragging = False
            prior_rect = None


    window.close()

main()
