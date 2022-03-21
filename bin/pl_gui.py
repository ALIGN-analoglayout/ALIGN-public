#!/usr/bin/env python
import numpy
import gdspy
import json
import argparse
import os
import PySimpleGUI as sg
import mip
import logging
logging.basicConfig(level='ERROR')

ap = argparse.ArgumentParser()
ap.add_argument( "-p", "--pl_file", type=str, default="", help='<filename.placement_verilog.json>')
args = ap.parse_args()
print(f"placement verilog : {args.pl_file}")

if args.pl_file == "":
    ap.print_help()
    exit()


class Point:
    def __init__(self, x = 0, y = 0):
        self._x = x
        self._y = y
    def __str__(self):
        return f'({self._x}, {self._y})'

    def transform(self, tr, w, h):
        x, y = tr._or._x + self._x, tr._or._y + self._y
        if tr._sX < 0: x -= w
        if tr._sY < 0: y -= h
        return Point(x, y)

    def moveto(self, x, y):
        self._x = x
        self._y = y

    def moveby(self, dx, dy):
        self._x += dx
        self._y += dy

class Rect:
    def __init__(self, ll = Point(), ur = Point):
        self._ll = ll
        self._ur = ur
    def __str__(self):
        return f'[{self._ll}--{self._ur}]'

    def fix(self):
        if self._ll._x > self._ur._x:
            self._ll._x, self._ur._x = self._ur._x, self._ll._x
        if self._ll._y > self._ur._y:
            self._ll._y, self._ur._y = self._ur._y, self._ll._y

    def transform(self, tr, w, h):
        ll = self._ll.transform(tr, w, h)
        ur = self._ur.transform(tr, w, h)
        r = Rect(ll, ur)
        r.fix()
        return r

    def xmin(self): return self._ll._x
    def ymin(self): return self._ll._y
    def xmax(self): return self._ur._x
    def ymax(self): return self._ur._y

    def width(self):
        return self._ur._x - self._ll._x

    def height(self):
        return self._ur._y - self._ll._y

    def moveby(self, dx, dy):
        self._ll.moveby(dx, dy)
        self._ur.moveby(dx, dy)

    def moveto(self, x, y):
        self._ur.moveby(x - self._ll._x, y - self._ll._y)
        self._ll.moveto(x, y)

    def overlapinx(self, r, strict = False):
        if strict:
           return self._ll._x < r._ur._x and self._ur._x > r._ll._x
        return self._ll._x <= r._ur._x and self._ur._x >= r._ll._x

    def overlapiny(self, r, strict = False):
        if strict:
           return self._ll._y < r._ur._y and self._ur._y > r._ll._y
        return self._ll._y <= r._ur._y and self._ur._y >= r._ll._y

    def overlap(self, r, strict = False):
        return self.overlapinx(r, strict) and self.overlapiny(r, strict)



class Transform:
    def __init__(self, oX = 0, oY = 0, sX = 1, sY = 1):
        self._or = Point(oX, oY) 
        self._sX = sX
        self._sY = sY
    def __str__(self):
        return f'({self._or} {self._sX} {self._sY})'

class Instance:
    def __init__(self, name = "", mname = "", tr = Transform(), modu = None):
        self._name = name
        self._mname = mname
        self._tr   = tr
        self._modu = modu
        self._gh   = None # gui handle
        self._th   = None # text handle
        self._bbox = modu._bbox.transform(self._tr, modu.width(), modu.height()) if modu else None
    def __str__(self):
        return f'{self._name} {str(self._tr)}'

    def width(self): return self._modu.width() if self._modu else 0
    def height(self): return self._modu.height() if self._modu else 0

    def setmodule(self, modu):
        if modu:
            self._modu = modu
            self._bbox = modu._bbox.transform(self._tr, modu.width(), modu.height())


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
        self._instgh    = dict()
        self._modified  = False
        self._constraints = dict()
    def __str__(self):
        s = f"{self._name} '{self._fname}' {self._cell}"
        for i in self._instances:
            s += f' [{str(i)} {i._modu._name}]'
        return s
    def width(self):
        return self._bbox.width()
    def height(self):
        return self._bbox.height()

modules = dict()
pldata = None
if args.pl_file:
    with open(args.pl_file) as fp:
        pldata = json.load(fp)
        for l in pldata.get("leaves"):
            lname = l.get("concrete_name")
            if lname:
                modu = Module(lname, True)
                bbox = l.get("bbox")
                modu._bbox = Rect(Point(bbox[0], bbox[1]), Point(bbox[2], bbox[3]))
                modules[modu._name] = modu
        for m in pldata.get("modules"):
            mname = m.get("concrete_name")
            if mname:
                modu = Module(mname)
                bbox = m.get("bbox")
                modu._bbox = Rect(Point(bbox[0], bbox[1]), Point(bbox[2], bbox[3]))
                for i in m.get("instances"):
                    iname = i.get("concrete_template_name")
                    trstr = i.get("transformation")
                    tr = Transform()
                    if trstr:
                        tr._or._x, tr._or._y = trstr["oX"], trstr["oY"]
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
            inst.setmodule(modules[inst._mname])
    maxdim = max(maxdim, m.width(), m.height()) * 1.02

def update_coord():
  for m in pldata.get("modules"):
      modu = modules[m.get("concrete_name")]
      if not modu._modified: continue
      bbox = [1e30, 1e30, 0, 0]
      for iname, inst in modu._instances.items():
          bbox[0] = min(bbox[0], inst._bbox._ll._x)
          bbox[1] = min(bbox[1], inst._bbox._ll._y)
          bbox[2] = max(bbox[2], inst._bbox._ur._x)
          bbox[3] = max(bbox[3], inst._bbox._ur._y)
      if m["bbox"] != bbox:
          m["bbox"] = bbox
      for i in m.get("instances"):
          iname = i.get("instance_name")
          inst = modu._instances[iname]
          trstr = i.get("transformation")
          trstr["oX"] = inst._bbox.xmin()  + (0 if trstr["sX"] > 0 else inst._modu.width())
          trstr["oY"] = inst._bbox.ymin()  + (0 if trstr["sY"] > 0 else inst._modu.height())


module_list = [k for k in modules if not modules[k]._leaf];
top_cell = module_list[0]
topm = modules[top_cell]

CSIZE = 800
def replot(top_name, window, graph):
    global topm
    global top_cell
    global undo_list
    global CSIZE
    CSIZE = int(min(window.size[0], window.size[1]) * 0.0099) * 100
    graph.erase()
    graph.set_size((CSIZE, CSIZE))
    graph.change_coordinates((0,0), (CSIZE,CSIZE))
    top_cell = top_name
    topm = modules[top_cell]
    for iname, inst in topm._instances.items():
        xl = inst._bbox._ll._x * CSIZE / maxdim
        yl = inst._bbox._ll._y * CSIZE / maxdim
        xh = inst._bbox._ur._x * CSIZE / maxdim
        yh = inst._bbox._ur._y * CSIZE / maxdim
        inst._gh = graph.draw_rectangle((xl, yl), (xh, yh), fill_color='#DEDEDE', line_color='red')
        topm._instgh[inst._gh] = inst
        inst._th = graph.draw_text(inst._name, ((xl + xh)/2, (yl + yh)/2), color = "black", font = None, angle = 0, text_location = "center")

def legalize(topm):
    model = mip.Model(sense=mip.MINIMIZE, solver_name=mip.CBC)
    x = [model.add_var(name = k + "_x", lb = 0, ub = 1e30) for k in topm._instances]
    y = [model.add_var(name = k + "_y", lb = 0, ub = 1e30) for k in topm._instances]
    area_x = model.add_var(name = "area_x", lb = 0, ub = 1e30)
    area_y = model.add_var(name = "area_y", lb = 0, ub = 1e30)
    model.objective = mip.minimize(area_x + area_y)
    ks = list(topm._instances.keys())
    for i in range(len(ks)):
        inst1 = topm._instances[ks[i]]
        model += area_x >= (x[i] + inst1.width())
        model += area_y >= (y[i] + inst1.height())
        for j in range(i + 1, len(ks)):
            inst2 = topm._instances[ks[j]]
            if inst2._bbox.overlapiny(inst1._bbox, True):
                if inst2._bbox.xmin() <= inst1._bbox.xmin():
                    model += x[j] + inst2._modu.width() <= x[i]
                else:
                    model += x[i] + inst1._modu.width() <= x[j]

            if inst2._bbox.overlapinx(inst1._bbox, True):
                if inst2._bbox.ymin() <= inst1._bbox.ymin():
                    model += y[j] + inst2._modu.height() <= y[i]
                else:
                    model += y[i] + inst1._modu.height() <= y[j]
    model.verbose = 0
    status = model.optimize(max_seconds=10)
    model.write('out.lp')
    if status == mip.OptimizationStatus.OPTIMAL:
        if model.num_solutions > 0:
            for i in range(len(x)):
                topm._instances[ks[i]]._bbox.moveto(x[i].x, y[i].x)

def rungui():
    undo_list = list()
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

    replot(module_list[0], window, graph)
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
            replot(values['-TOP-'], window, graph)
            #undo_list = list()
        elif event is '-UNDO-':
            if undo_list:
                op = undo_list.pop()
                if op:
                    inst = op[0]
                    graph.move_figure(inst._gh, (-inst._bbox._ll._x + op[1]) * CSIZE / maxdim, (-inst._bbox._ll._y + op[2]) * CSIZE / maxdim)
                    graph.move_figure(inst._th, (-inst._bbox._ll._x + op[1]) * CSIZE / maxdim, (-inst._bbox._ll._y + op[2]) * CSIZE / maxdim)
                    inst._bbox.moveto(op[1], op[2])
                     #inst._tr._or._x = op[1]
                     #inst._tr._or._y = op[2]
        elif event is '-SAVE-':
            update_coord()
        elif event is '-LGL-':
            legalize(topm)
            replot(values['-TOP-'], window, graph)
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
                        undo_list.append([movedinst, movedinst._bbox._ll._x, movedinst._bbox._ll._y])
                        movedinst._bbox.moveby(dx * maxdim / CSIZE, dy * maxdim / CSIZE)
                topm._modified = True
            start_point, end_point = None, None  # enable grabbing a new rect
            dragging = False
            drag_figures = []


    window.close()

rungui()
