import os
import json
import pathlib
from copy import deepcopy
import shutil
import align.pdk.finfet
import re
import math
import matplotlib.pyplot as plt
import matplotlib
matplotlib.use('Agg')

align_home = os.getenv('ALIGN_HOME')

my_dir = pathlib.Path(__file__).resolve().parent

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


def build_example(name, netlist, netlist_setup, constraints):
    example = my_dir / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)
    example.mkdir(parents=True)
    with open(example / f'{name}.sp', 'w') as fp:
        fp.write(netlist)
    with open(example / f'{name}.setup', 'w') as fp:
        fp.write(netlist_setup)
    with open(example / f'{name}.const.json', 'w') as fp:
        fp.write(json.dumps(constraints, indent=2))
    return example


def run_example(example, n=8, cleanup=True, max_errors=0, log_level='INFO', area=None, additional_args=None):
    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir), '-l', log_level, '-n', str(n)]

    if additional_args:
        for elem in additional_args:
            args.append(elem)

    results = align.CmdlineParser().parse_args(args)

    assert results is not None, f"{example.name}: No results generated"

    for result in results:
        _, variants = result
        for (k, v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {example.name} ({k})"
            assert v['errors'] <= max_errors, f"{example.name} ({k}):Number of DRC errorrs: {str(v['errors'])}"

    name = example.name.upper()

    verify_abstract_names(name, run_dir)

    verify_area(name, run_dir, area=area)

    if cleanup:
        shutil.rmtree(run_dir)
        shutil.rmtree(example)
    else:
        return (example, run_dir)


def verify_abstract_names(name, run_dir):
    """ Make sure that there are no unused abstract_template_name's """
    with (run_dir / '1_topology' / '__primitives__.json').open('rt') as fp:
        primitives = json.load(fp)
        abstract_names = {v['abstract_template_name'] for v in primitives.values()}

    with (run_dir / '1_topology' / f'{name}.verilog.json').open('rt') as fp:
        verilog_json = json.load(fp)
        abstract_names_used = list()
        for module in verilog_json['modules']:
            abstract_names_used += [i['abstract_template_name'] for i in module['instances']]
        abstract_names_used = set(abstract_names_used)
    assert abstract_names.issubset(abstract_names_used), (
        f'__primitives__.json has unused primitives: {set.difference(abstract_names, abstract_names_used)}\n'
    )


def verify_area(name, run_dir, area=None):
    json_file = run_dir / '3_pnr' / f'{name}_0.json'
    if json_file.exists():
        with json_file.open('rt') as fp:
            layout = json.load(fp)
            x0, y0, x1, y1 = layout['bbox']
            area_0 = (x1-x0)*(y1-y0)
            print(f'{name}: area is {area_0}')
            if area is not None and area > 0:
                assert area_0 <= area, (f'Placer found a suboptimal solution: area: {area_0} target: {area} ratio: {area_0/area}')


def _parse_sa_cost(name):
    """
        logger->debug("sa__cost name={0} t_index={1} effort={2} cost={3}", designData.name, T_index, i, curr_cost);
    """
    pattern = f'sa__cost name={name}'
    cost = []
    temp = []
    with open(my_dir / 'LOG' / 'align.log', 'r') as fp:
        for line in fp:
            if re.search(pattern, line):
                line = line.split(pattern)[1]
                val = float(line.split('cost=')[1])
                cost.append(val)
                val = line.split('t_index=')[1]
                val = float(val.split(' ')[0])
                temp.append(val)
    return temp, cost


def plot_sa_cost(name, normalize=False):
    t, c = _parse_sa_cost(name)
    if normalize:
        c_norm = [100*math.exp(v - c[0]) for v in c]
    else:
        c_norm = c
    plt.figure()
    plt.plot(range(len(c_norm)), c_norm)
    plt.title('Cost')
    if normalize:
        plt.ylabel('Cost normalized to initial solution (%)')
    else:
        plt.ylabel('Cost')
    plt.xlabel('Perturbation')
    plt.legend([f'initial={c_norm[0]:.3f} final={c_norm[-1]:.3f} min={min(c_norm):.3f}'])
    plt.grid()
    plt.show()
    plt.savefig(f'{my_dir}/cost_{name}.png')
