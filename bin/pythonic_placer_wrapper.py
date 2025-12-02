#!/usr/bin/env python
import json
import plotly.graph_objects as go
import plotly.express as px

from align.pnr.placer_pythonic import pythonic_placer, propagate_down_global_signals, trim_placement_data
from align.cell_fabric.transformation import Transformation, Rect

def draw_placement(placement_data, module_name):
    leaves = {x['concrete_name']: x for x in placement_data['leaves']}
    modules = {x['concrete_name']: x for x in placement_data['modules']}
    module = modules[module_name]

    colorscale = px.colors.qualitative.Alphabet

    fig = go.Figure()
    fig.update_xaxes(range=[0, max(module['bbox'])])
    fig.update_yaxes(range=[0, max(module['bbox'])])

    # Add shapes
    x_lst = list()
    y_lst = list()
    n_lst = list()

    i = 0
    for instance in module['instances']:
        concrete_name = instance['concrete_template_name']

        if concrete_name in leaves:
            bbox = leaves[concrete_name]['bbox']
        elif concrete_name in modules:
            bbox = modules[concrete_name]['bbox']
        else:
            assert False

        bbox = Transformation( instance['transformation']['oX'], instance['transformation']['oY'],
            instance['transformation']['sX'], instance['transformation']['sY']).hitRect(Rect(*bbox)).canonical().toList()

        llx, lly, urx, ury = bbox

        color = colorscale[i % len(colorscale)]
        fig.add_shape(type="rect", x0=llx, y0=lly, x1=urx, y1=ury, line=dict(color="RoyalBlue", width=3), fillcolor=color)
        i += 1
        x_lst.append((llx+urx)/2)
        y_lst.append((lly+ury)/2)
        n_lst.append(f"{instance['instance_name']}")

    fig.update_shapes(opacity=0.5, xref="x", yref="y")

    # Add labels
    fig.add_trace(go.Scatter(x=x_lst, y=y_lst, text=n_lst, mode="text", textfont=dict(color="black", size=24)))

    fig.show()


def placer_wrapper(verilog, top, vmap, inputs, output, draw):
    with open(verilog, 'r') as fp:
        input_data = json.load(fp)
    with open(vmap, 'r') as fp:
        lines = fp.readlines()
        for line in lines:
            line = line.split()
            ln = line[1].replace(".gds", "")
            with open(f'{inputs}/{ln}.json', 'r') as fp1:
                leaf_json = json.load(fp1)
                leaf_data = {'abstract_template_name':line[0], 'concrete_template_name':ln}
                leaf_data['bbox'] = leaf_json['bbox'] if 'bbox' in leaf_json else None
                leaf_data['terminals'] = [t for t in leaf_json['terminals'] if t['netType'] == 'pin'] if 'terminals' in leaf_json else None
                leaf_data['constraints'] = []
                if 'leaves' not in input_data:
                    input_data['leaves'] = []
                input_data['leaves'].append(leaf_data)
    
    #with open('placement_input.json', "wt") as fp:
    #    fp.write(json.dumps(input_data, indent=2) + '\n')
    placement_data = pythonic_placer(top, input_data)
    placement_data = trim_placement_data(placement_data, top)
    with open(output, "wt") as fp:
        json.dump(placement_data, fp=fp, indent=2)
    if draw: draw_placement(placement_data, f'{top}_0')

if __name__ == '__main__':
  import argparse
  ap = argparse.ArgumentParser()
  ap.add_argument( "-v", "--verilog", type=str, default="", help='<filename.verilog.json>')
  ap.add_argument( "-t", "--top", type=str, default="", help='<top module name>')
  ap.add_argument( "-m", "--map", type=str, default="", help='<map file in the 3_pnr/inputs directory>')
  ap.add_argument( "-i", "--inputs", type=str, default="3_pnr/inputs", help='<path of 3_pnr/inputs directory>')
  ap.add_argument( "-o", "--output", type=str, default="placement_output.json", help='<output placement file>')
  ap.add_argument( "-d", "--draw", action='store_true', help='<draw layout on browser canvas>')
  args = ap.parse_args()
  print(f"verilog file : {args.verilog}")
  print(f"map file     : {args.map}")
  print(f"top module   : {args.top}")
  print(f"input dir    : {args.inputs}")
  print(f"output       : {args.output}")
  if args.verilog == "" or args.inputs == "" or args.map == "" or args.top == "":
      ap.print_help()
      exit()
  placer_wrapper(args.verilog, args.top, args.map, args.inputs, args.output, args.draw)
