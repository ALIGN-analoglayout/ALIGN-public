import os
import json
import pathlib

align_home = os.getenv('ALIGN_HOME')

my_dir = pathlib.Path(__file__).resolve().parent


def _canvas_to_data(c):
    if hasattr(c, "computeBbox"):
        c.computeBbox()
        data = {'bbox': c.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c.removeDuplicates(allow_opens=True)}
    else:
        data = c
    for k in ['globalRoutes', 'globalRouteGrid']:
        if k not in data:
            data[k] = []
    return data


def export_to_viewer(fn, c):
    if align_home:
        data = _canvas_to_data(c)
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')


def compare_with_golden(fn, c):

    data = _canvas_to_data(c)

    export_to_viewer(fn, data)

    with open(my_dir / (fn + "-cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "-freeze.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2
