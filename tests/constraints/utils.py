import os
import json
import pathlib
from copy import deepcopy
import shutil
import align.pdk.finfet
import re

align_home = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_WORK_DIR' in os.environ:
    my_dir = pathlib.Path(os.environ['ALIGN_WORK_DIR']).resolve()
else:
    my_dir = align_home / 'tests' / 'tmp'

pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent


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
        return data


def compare_with_golden(fn, c):

    data = _canvas_to_data(c)

    export_to_viewer(fn, data)

    with open(my_dir / (fn + "-cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "-freeze.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def place(cv, c, ox, oy):
    data = _canvas_to_data(c)
    for term in data["terminals"]:
        new_term = deepcopy(term)
        x0, y0, x1, y1 = term['rect']
        new_term['rect'] = [x0+ox, y0+oy, x1+ox, y1+oy]
        cv.terminals.append(new_term)


def get_test_id():
    try:
        t = os.environ.get('PYTEST_CURRENT_TEST')
        t = t.split(' ')[0].split(':')[-1]
        t = t.replace('[', '_').replace(']', '').replace('-', '_')
        t = t[5:]
    except BaseException:
        t = 'debug'
    return t


def build_example(name, netlist, constraints):
    example = my_dir / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)
    example.mkdir(parents=True)
    with open(example / f'{name}.sp', 'w') as fp:
        fp.write(netlist)
    with open(example / f'{name}.const.json', 'w') as fp:
        fp.write(json.dumps(constraints, indent=2))
    return example

def _count_pattern(pattern):
    data = set()
    with open(my_dir / 'LOG' / 'align.log', 'r') as fp:
        for line in fp:
            if re.search(pattern, line):
                line = line.split(pattern)[1]
                data.add(line)
    return len(data)


def run_example(example, n=8, cleanup=True, max_errors=0, log_level='INFO'):
    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir), '-l', log_level, '-n', str(n)]
    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f"{example.name}: No results generated"

    for result in results:
        _, variants = result
        for (k, v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {example.name} ({k})"
            assert v['errors'] <= max_errors, f"{example.name} ({k}):Number of DRC errorrs: {str(v['errors'])}"

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(example)
    else:
        return (example, run_dir)
