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
        self._lk   = None # lock icon handle
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

lock50  = b'iVBORw0KGgoAAAANSUhEUgAAAAoAAAAOCAQAAAC8qkUgAAAAAmJLR0QA/4ePzL8AAAAJcEhZcwAAADIAAAAyADmg1OUAAAAHdElNRQfmAxYGMRzoygfjAAAAfklEQVQY06XOoQ3CQABG4XdHQupgBMIEJCzQrc4zS/coG7QSA0gCjlQcou1DkQDF8X73qR8RNjScadiJCMKKO25di1QvrHGvZJPcRIKEC4u2GAJ0Yzk4hwgEZp392I9XMCSAGr+WApmCz9o4IVhGfvQfPiKnCR6g5Pj2MVPLEwOjQ+ZPJN+IAAAAJXRFWHRkYXRlOmNyZWF0ZQAyMDIyLTAzLTIyVDExOjQ5OjI4LTA1OjAwTh6m8QAAACV0RVh0ZGF0ZTptb2RpZnkAMjAyMi0wMy0yMlQxMTo0OToyOC0wNTowMD9DHk0AAAAUdEVYdHBkZjpWZXJzaW9uAFBERi0xLjUgBVwLOQAAAABJRU5ErkJggg=='
lock100 = b'iVBORw0KGgoAAAANSUhEUgAAABMAAAAbCAQAAAA0CnwqAAAAAmJLR0QA/4ePzL8AAAAJcEhZcwAAAGQAAABkAA+Wxd0AAAAHdElNRQfmAxYGMDYqav90AAAA8klEQVQ4y+3RMU4CQRTG8f+uEhISYralIjQeYC+w9pTQUdDZ0uIxvIDWVhSegW7trSjXjmwCOgvqR/GEHcC4ewDfFPPevN9kkjeI/WJEfigcGYnXOyT3bNHRcoxPGAmflsYaaqjIjtdEx2xhyUxOQix1Y41njxGxQuhO5YtL23Kfjay38FihWAhn1SVe5Lxon7fpkMJPbezNiiu6QXnpQ8C3z2754gIGRCpZCtAKMvpKEcxP5qWz+cUwZlPBRAZZJRIupEV1NEO2NRhhHfTPfmHNeuy1hiqgx7ry6x8QTP6EG+YiEBD0eOKa4uyxBu9M9Qg7xVnlUXrM3VEAAAAldEVYdGRhdGU6Y3JlYXRlADIwMjItMDMtMjJUMTE6NDg6NTQtMDU6MDBsua6iAAAAJXRFWHRkYXRlOm1vZGlmeQAyMDIyLTAzLTIyVDExOjQ4OjU0LTA1OjAwHeQWHgAAABR0RVh0cGRmOlZlcnNpb24AUERGLTEuNSAFXAs5AAAAAElFTkSuQmCC'
lock200 = b'iVBORw0KGgoAAAANSUhEUgAAACcAAAA3CAQAAAAlfJslAAAAAmJLR0QA/4ePzL8AAAAJcEhZcwAAAMgAAADIAGP6560AAAAHdElNRQfmAxYHFieCxjaVAAABoUlEQVRYw+2XsVLCQBCGv2SspEphaWHGyjavkMo+hT4AtY9AiRWPgJVvoBUFZRosncFxKB0GCinMoAWuRQT2MBcCnDPOyG6Ry/25L7u52+SCYHMCEloMFx09mkT26wXBLiS8FQop4YY4ArolIbzT2ABHQlaaUR5jUAlHyHQtTJiRVsM9VoDlXpCyJ2jzWlwZHQQkRIQM6NDhVUsfnMnAvNqMLFq9XSKZLE8ziU29V5osLVO9kbUZRmW4oRlZ8SNTEc5oWnGE5rjMgnspSVc361qJLTBBjLIwFV/NyoWeohi7JVblQLUnWjglk3HhkGNOKuH6Wnim5tUsgyZiw/k4Ncc4neyhFq7pWFPqqbaXcqlKbbFMGpVLf9Wny1KZH9KtYbm3FW61Vrfyxjfu53tky5TDHNd3ghNSARJHMEGIfc6dLbpPYo8RR86ADx6yO2Vpf7tm97g9bo/b4/4Pbrw7ZGFPPh2HuHufrkPcHQSMHH20+/mmInaEi35jByUQbPCfaN3uLHACwU4RtuYN1Ue81aT09W+eoRBQ57YydESbxOz6Apjmq4/ub+k3AAAAJXRFWHRkYXRlOmNyZWF0ZQAyMDIyLTAzLTIyVDEyOjIyOjM5LTA1OjAwiVzwoQAAACV0RVh0ZGF0ZTptb2RpZnkAMjAyMi0wMy0yMlQxMjoyMjozOS0wNTowMPgBSB0AAAAUdEVYdHBkZjpWZXJzaW9uAFBERi0xLjUgBVwLOQAAAABJRU5ErkJggg=='
lock400 = b'iVBORw0KGgoAAAANSUhEUgAAAE4AAABuCAQAAAAjD+2gAAAAAmJLR0QA/4ePzL8AAAAJcEhZcwAAAZAAAAGQAFbw2+gAAAAHdElNRQfmAxYHFjF2EoPEAAADLElEQVR42u2bu5HbMBCGf3AcecYBxoFnHPJKoEtgC7Q7YAt0CXIJcglUCboSqNSRxcyhycAFrAOJehKvJUhibrAb3B2woL7DEoCwsysIU0QUyJBBIrs0tWhxQIsd9ZMeDQDEUkiUqA1GDSqkvOefP4UFtnEw3yNbCA4SG3TOn7LlzaCbccEAG3QzK5yTM8e0hpwFDhLbiWgEQuPmXlu0xgMagdC5LA87I19ojng2Jj4ceu9cy3fPbFB5RiMQai9wyGdAI1huLEJ/torm5tQ0SA4A6HGwM3+hdtLZitJmFlKqqKaOhoYjbakk42u1nehWHM1oGxrv6KgyjTWuWl2X8UTIqCGdQa2fv/0UOMO8bcj0cEJHha7bcF6oOzL951YWaEbvGTzPdGpKvTVco3Zuw4XTHll7azSCdlPTvpSq5tSPSwfNVR2lblSi2P60W2/lfFMpVR2pbhQDLocUrnCFaoR2EhI4S+4+BEAx3syauW/qIdaHrc0oFtwH9ZDc2ancf+kdaxrQ018H6894Lz55hPuNj7phUsgFZkHl1n+MZ2nlj0e4ICTCRbiT9Kx4IyeSyFjhX5Ez8H4q2kWN78p7mOIL0y/H70TTVBG/G2ua445v0g4jl43nBt+REXt9ulHc/+Ev1MV0rxJudbQnvDAcqnDu9ZepEV9/elkaw4+5Ql0c7YYL4wC3Xx3pVrc3cHahrkU1vcJZhLoW1voMF+C8EQjZ6cbPu4jOLTkgjGHhteRAXxJRTH/OLJKJNAnUqQBQJPqAwKoiE2boYwnJErhe3ZcTKRDmWgXw9q6GES7CRbgIF+Ei3NoS4SJchItwES7CRbgIF4ZEuAgX4SLcG4drA4d7XZtBKYeElSqzjPQhz9yrgES3NsWotPSSUB/o3O1OW0mwcCBATqggnEv3BEICUK/MH1tPfgC4pG6ElYJwLoAZ4MJKQkjv4ILJZCLcZDNd4ULIASPc5YHdtAaxau+qcu56kK2M91C/+dC7qnO3j+VCTxaeCpTddaTEadQO5cL73n68vElpz6rX5+hRXV6lGQWJauakv1pf92XMshISBXJIj2lFPQ5o8Uo7k+F/3fkd8GNw0bkAAAAldEVYdGRhdGU6Y3JlYXRlADIwMjItMDMtMjJUMTI6MjI6NDktMDU6MDCDmfm4AAAAJXRFWHRkYXRlOm1vZGlmeQAyMDIyLTAzLTIyVDEyOjIyOjQ5LTA1OjAw8sRBBAAAABR0RVh0cGRmOlZlcnNpb24AUERGLTEuNSAFXAs5AAAAAElFTkSuQmCC'
CSIZE = 800
def replot(top_name, window, graph):
    global topm
    global top_cell
    global undo_list
    global CSIZE
    cs = CSIZE
    CSIZE = int(min(window.size[0], window.size[1]) * 0.0099) * 100
     #graph.erase()
    graph.set_size((CSIZE, CSIZE))
    graph.change_coordinates((0,0), (CSIZE,CSIZE))
    top_cell = top_name
    topm = modules[top_cell]
    for iname, inst in topm._instances.items():
        xl = inst._bbox._ll._x * CSIZE / maxdim
        yl = inst._bbox._ll._y * CSIZE / maxdim
        xh = inst._bbox._ur._x * CSIZE / maxdim
        yh = inst._bbox._ur._y * CSIZE / maxdim
        graph.delete_figure(inst._gh)
        if inst._lk: graph.delete_figure(inst._lk)
        graph.delete_figure(inst._th)
        inst._gh = graph.draw_rectangle((xl, yl), (xh, yh), fill_color='#DEDEDE', line_color='red')
        if inst._lk: inst._lk = graph.draw_image(data=lock100, location=((xl + xh)/2, (yl + yh)/2.1))
        topm._instgh[inst._gh] = inst
        inst._th = graph.draw_text(inst._name, ((xl + xh)/2, (yl + yh)/2), color = "black", font = None, angle = 0, text_location = "center")
    graph.update()

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
        if inst1._lk:
            model += x[i] == inst1._bbox.xmin()
            model += y[i] == inst1._bbox.ymin()
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
     #sg.theme('Dark Blue 3')

    newpl_file = (args.pl_file[0:args.pl_file.find('.placement_verilog.json')] + "_1" + ".placement_verilog.json")
    if not module_list:
        exit()
    global top_cell, topm
    top_cell = module_list[0]
    topm = modules[top_cell]

    col = [
      [sg.Combo(module_list, default_value = module_list[0], enable_events = True, key = '-TOP-', size = (max(max([len(k) for k in module_list]), 30), 6), readonly = True, auto_size_text = True)],
      [sg.Button('Lock', key='-LOCK-', button_color = ('black')),
      sg.Button('Undo', key='-UNDO-', button_color = ('black')),
      sg.Button('Legalize', key='-LGL-', button_color = ('black'))],
      [sg.Button('Save Changes', key='-SAVE-', button_color = ('black'))],
      [sg.Button('Write', key='-WRITE-', button_color = ('black')), sg.Text('Write to file : '), sg.InputText(newpl_file, key='-FN-')]
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
    lockmode = False
    while True:
        event, values = window.read()
        if event is None:
            break  # exit
        elif not event.startswith('-GRAPH-'):
            graph.Widget.config(cursor='left_ptr')

        if event is '-LOCK-':
            if not lockmode:
                for k in ['-UNDO-', '-LGL-', '-SAVE-', '-WRITE-']:
                    window[k].update(button_color=('gray'), disabled=True)
            else:
                for k in ['-UNDO-', '-LGL-', '-SAVE-', '-WRITE-']:
                    window[k].update(button_color=('black'), disabled=False)
            lockmode = ~lockmode
            continue
        if lockmode:
            if event is '-GRAPH-':
                x, y = values["-GRAPH-"]
                continue
            if event.endswith('+UP'):
                figs = graph.get_figures_at_location((x,y))
                for fig in figs:
                    if fig in topm._instgh:
                        inst = topm._instgh[fig]
                        if inst._lk:
                            graph.delete_figure(inst._lk)
                            inst._lk = None
                        else:
                            xl = inst._bbox._ll._x * CSIZE / maxdim
                            yl = inst._bbox._ll._y * CSIZE / maxdim
                            xh = inst._bbox._ur._x * CSIZE / maxdim
                            yh = inst._bbox._ur._y * CSIZE / maxdim
                            inst._lk = graph.draw_image(data=lock100, location=((xl + xh)/2, (yl + yh)/2.1))
                graph.update()
                continue
        elif event in ('-TOP-', '-RESIZE-'):
            if event is '-RESIZE-':
                if winsize == window.size: continue
                else: winsize = window.size
             #topm._instgh = dict()
             #for iname, inst in topm._instances.items():
             #   inst._gh = inst._th = None
            replot(values['-TOP-'], window, graph)
            #undo_list = list()
        elif event is '-UNDO-':
            if undo_list:
                op = undo_list.pop()
                if op:
                    inst = op[0]
                    graph.move_figure(inst._gh, (-inst._bbox._ll._x + op[1]) * CSIZE / maxdim, (-inst._bbox._ll._y + op[2]) * CSIZE / maxdim)
                    graph.move_figure(inst._th, (-inst._bbox._ll._x + op[1]) * CSIZE / maxdim, (-inst._bbox._ll._y + op[2]) * CSIZE / maxdim)
                    if inst._lk: graph.move_figure(inst._lk, (-inst._bbox._ll._x + op[1]) * CSIZE / maxdim, (-inst._bbox._ll._y + op[2]) * CSIZE / maxdim)
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
                       if movedinst._lk: graph.move_figure(movedinst._lk, delta_x, delta_y)
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
