#!/usr/bin/env python
import numpy
import gdspy
import json
import argparse
import os
import PySimpleGUI as sg

ap = argparse.ArgumentParser()
ap.add_argument( "-p", "--pl_file", type=str, default="", help='<filename.placement_verilog.json>')
args = ap.parse_args()
print(f"placement verilog : {args.pl_file}")

if args.pl_file == "":
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
    def __init__(self, name = "", mname = "", tr = Transform(), modu = None):
        self._name = name
        self._mname = mname
        self._tr   = tr
        self._modu = modu
        self._gh   = None # gui handle
        self._th   = None # text handle
    def __str__(self):
        return f'{self._name} {str(self._tr)}'


class Constraint:
    def __init__(self, name = ""):
        self._name = name
        self._instances = list()
        self._attr = dict()

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
        self._instgh    = dict()
        self._modified  = False
        self._constraints = dict()
    def __str__(self):
        s = f"{self._name} '{self._fname}' {self._cell}"
        for i in self._instances:
            s += f' [{str(i)} {i._modu._name}]'
        return s

modules = dict()
pldata = None
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
                        modu._instances[i.get("instance_name")] = Instance(i.get("instance_name"), iname, tr)
                if "constraints" in m:
                    for c in m.get("constraints"):
                        cname = c.get("constraint")
                        if cname in ("symmetric_blocks", "align", "order") and cname not in modu._constraints:
                                modu._constraints[cname] = list()
                        if "instances" in c and cname in modu._constraints:
                            modu._constraints[cname].append(Constraint(m.get("instances")))
                modules[modu._name] = modu
maxdim = 0
for mname in modules:
    m = modules[mname]
    for iname in m._instances:
        inst = m._instances[iname]
        if not inst._modu:
            inst._modu = modules[inst._mname]
            inst._width = inst._modu._width
            inst._height = inst._modu._height
            if inst._tr._sX < 0:
                inst._tr._oX -= inst._width
            if inst._tr._sY < 0:
                inst._tr._oY -= inst._height
    maxdim = max(maxdim, m._width, m._height) * 1.02

def update_coord():
  for m in pldata.get("modules"):
      modu = modules[m.get("concrete_name")]
      if not modu._modified: continue
      bbox = [1e30, 1e30, 0, 0]
      for iname, inst in modu._instances.items():
          bbox[0] = min(bbox[0], inst._tr._oX)
          bbox[1] = min(bbox[1], inst._tr._oY)
          bbox[2] = max(bbox[2], inst._tr._oX + inst._modu._width)
          bbox[3] = max(bbox[3], inst._tr._oY + inst._modu._height)
      if m["bbox"] != bbox:
          m["bbox"] = bbox
      for i in m.get("instances"):
          iname = i.get("instance_name")
          inst = modu._instances[iname]
          trstr = i.get("transformation")
          trstr["oX"] = inst._tr._oX
          if trstr["sX"] < 0:
              trstr["oX"] += inst._modu._width
          trstr["oY"] = inst._tr._oY
          if trstr["sY"] < 0:
              trstr["oY"] += inst._modu._height

module_list = [k for k in modules if not modules[k]._leaf];
top_cell = module_list[0]
topm = modules[top_cell]
CSIZE = 800
def main():

    oper = list()
    sg.theme('Dark Blue 3')

    newpl_file = (args.pl_file[0:args.pl_file.find('.placement_verilog.json')] + "_1" + ".placement_verilog.json")
    if not module_list:
        exit()
    global top_cell, topm
    top_cell = module_list[0]
    topm = modules[top_cell]

    col = [
      [sg.Combo(module_list, default_value = module_list[0], enable_events = True, key = '-TOP-', size = (max(max([len(k) for k in module_list]), 30), 6), readonly = True, auto_size_text = True)],
      [sg.Button('Undo', key='-UNDO-')],
      [sg.Button('Legalize', key='-LGL-')],
      [sg.Button('Save', key='-SAVE-')],
      [sg.Button('Write', key='-WRITE-'), sg.Text('Write to file : '), sg.InputText(newpl_file, key='-FN-')]
    ]

    layout = [[sg.Graph(
        canvas_size=(CSIZE, CSIZE),
        graph_bottom_left=(0, 0),
        graph_top_right=(CSIZE, CSIZE),
        key="-GRAPH-",
        change_submits=True,  # mouse click events
        background_color='lightblue',
        drag_submits=True), sg.Col(col) ],
        [sg.Text(key='info', size=(80, 1))]]

    window = sg.Window("Drag and move cells", layout, finalize=True, resizable = True, border_depth=5)
    window.bind('<Configure>',"-RESIZE-")
    graph = window["-GRAPH-"] 
    graph.expand(expand_x = True, expand_y = True)

    winsize = window.size

    def replot(top_name):
        global topm
        global top_cell
        global oper
        global CSIZE
        CSIZE = int(min(window.size[0], window.size[1]) * 0.0099) * 100
        graph.erase()
        graph.set_size((CSIZE, CSIZE))
        graph.change_coordinates((0,0), (CSIZE,CSIZE))
        top_cell = top_name
        topm = modules[top_cell]
        for iname, inst in topm._instances.items():
            x = inst._tr._oX * CSIZE / maxdim
            y = inst._tr._oY * CSIZE / maxdim
            w = inst._modu._width * CSIZE / maxdim
            h = inst._modu._height * CSIZE / maxdim
            inst._gh = graph.draw_rectangle((x, y), (x + w, y + h), fill_color='#DEDEDE', line_color='red')
            topm._instgh[inst._gh] = inst
            inst._th = graph.draw_text(inst._name, (x + w/2, y + h/2), color = "black", font = None, angle = 0, text_location = "center")

    replot(module_list[0])
    dragging = False
    start_point = end_point = None
    drag_figures = []
    graph.bind('<Button-3>', '+RIGHT+')
    movedinst = None
    while True:
        event, values = window.read()
        if event is None:
            break  # exit
        elif not event.startswith('-GRAPH-'):
            graph.Widget.config(cursor='left_ptr')

        if event in ('-TOP-', '-RESIZE-'):
            if event is '-RESIZE-':
                if winsize == window.size: continue
                else: winsize = window.size
            topm._instgh = dict()
            for iname, inst in topm._instances.items():
                inst._gh = inst._th = None
            replot(values['-TOP-'])
            #oper = list()
        elif event is '-UNDO-':
            if oper:
                op = oper.pop()
                if op:
                    inst = op[0]
                    graph.move_figure(inst._gh, (-inst._tr._oX + op[1]) * CSIZE / maxdim, (-inst._tr._oY + op[2]) * CSIZE / maxdim)
                    graph.move_figure(inst._th, (-inst._tr._oX + op[1]) * CSIZE / maxdim, (-inst._tr._oY + op[2]) * CSIZE / maxdim)
                    inst._tr._oX = op[1]
                    inst._tr._oY = op[2]
        elif event is '-SAVE-':
            update_coord()
        elif event is '-WRITE-':
            info = window["info"]
            fp = open(values["-FN-"], "w")
            if fp:
                info.update(value=f'saving placement to file : {values["-FN-"]}')
                json.dump(pldata, fp, indent=4)
                fp.close()
            else:
                info.update(value=f'unable to write to file : {values["-FN-"]}')
        elif event == "-GRAPH-":
            x, y = values["-GRAPH-"]
            if not dragging:
                start_point = (x, y)
                dragging = True
                drag_figures = graph.get_figures_at_location((x,y))
                lastxy = x, y
            else:
                end_point = (x, y)

            delta_x, delta_y = x - lastxy[0], y - lastxy[1]
            lastxy = x,y
            if None not in (start_point, end_point):
               for fig in drag_figures:
                   if fig in topm._instgh:
                       movedinst = topm._instgh[fig]
                       graph.move_figure(fig, delta_x, delta_y)
                       graph.move_figure(movedinst._th, delta_x, delta_y)
                   graph.update()
        elif event.endswith('+UP'):
            info = window["info"]
            if None not in (start_point, end_point):
                dx = end_point[0] - start_point[0]
                dy = end_point[1] - start_point[1]
                topm._modified = True
                for fig in drag_figures:
                    if fig in topm._instgh:
                        movedinst = topm._instgh[fig]
                        info.update(value=f"grabbed {movedinst._name} from {start_point} to {end_point}")
                        oper.append([movedinst, movedinst._tr._oX, movedinst._tr._oY])
                        movedinst._tr._oX += int(dx * maxdim / CSIZE)
                        movedinst._tr._oY += int(dy * maxdim / CSIZE)
                topm._modified = True
            start_point, end_point = None, None  # enable grabbing a new rect
            dragging = False
            drag_figures = []


    window.close()

main()
