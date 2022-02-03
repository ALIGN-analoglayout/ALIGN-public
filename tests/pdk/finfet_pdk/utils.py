import os
import json
import pathlib
from copy import deepcopy
import shutil
import align.pdk.finfet
import re
import math
try:
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
except ImportError:
    plt = None

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


def build_example(name, netlist, constraints):
    example = my_dir / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)
    example.mkdir(parents=True)
    with open(example / f'{name}.sp', 'w') as fp:
        fp.write(netlist)
    if isinstance(constraints, dict):
        for k, v in constraints.items():
            with open(example / f'{k}.const.json', 'w') as fp:
                fp.write(json.dumps(v, indent=2))
    else:
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
            if elem:
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
                # assert area_0 <= area, (f'Placer found a suboptimal solution: area: {area_0} target: {area} ratio: {area_0/area}')
                print(f'Target area: {area} Current area: {area_0} Current/Target: {area_0/area}')


def _parse_pattern(pattern):
    """
    logger->debug("sa__cost name={0} t_index={1} effort={2} cost={3} temp={4}", designData.name, T_index, 0, curr_cost, T);
    logger->debug("sa__seq__hash name={0} {1} cost={2} temp={3} t_index={4}", designData.name, trial_sp.getLexIndex(designData), trial_cost, T, T_index);
    """
    data = dict()
    with open(my_dir / 'LOG' / 'align.log', 'r') as fp:
        for line in fp:
            if re.search(pattern, line):
                line = line.split(pattern)[1]
                line = line.strip().split()
                for item in line:
                    k, v = item.split('=')
                    if k not in data:
                        data[k] = []
                    else:
                        data[k].append(float(v))
    # for k, v in data.items():
    #     print(f'{k}: min={min(v)} max={max(v)}')
    return data


def plot_sa_cost(name):
    assert plt is not None, "Need to install matplotlib to use this feature"
    data = _parse_pattern(f'sa__cost name={name}')

    init = -1
    for i in data['cost']:
        if i > 0:
            init = i
            break
    assert init > 0

    cost = [math.exp(k-init) if k > 0 else -1 for k in data['cost']]

    fig, ax = plt.subplots(2, 1)

    ax[0].plot(range(len(cost)), cost, '-o')
    ax[0].set_xlim(0, len(cost)+1)
    ax[0].set_ylabel('Cost norm. to initial')
    ax[0].set_xlabel('Iteration')
    ax[0].legend([f'initial={cost[0]:.3f} final={cost[-1]:.3f} min={min(cost):.3f}'])
    ax[0].grid()

    ax[1].plot(data['temp'], cost, '-o')
    ax[1].set_xlim(data['temp'][0], data['temp'][-1])
    ax[1].set_ylabel('Cost norm. to initial')
    ax[1].set_xlabel('Temperature')
    ax[1].legend([f'initial={cost[0]:.3f} final={cost[-1]:.3f} min={min(cost):.3f}'])
    ax[1].grid()

    fig.set_size_inches(14, 8)
    fig.savefig(f'{my_dir}/{name}_cost_trajectory.png', dpi=300, pad_inches=0.1)


def plot_sa_seq(name):
    assert plt is not None, "Need to install matplotlib to use this feature"
    data = _parse_pattern(f'sa__seq__hash name={name}')

    init = -1
    for i in data['cost']:
        if i > 0:
            init = i
            break
    assert init > 0

    cost = [math.exp(k-init) if k > 0 else -1 for k in data['cost']]
    cm = plt.cm.get_cmap('cool')

    fig, ax = plt.subplots(1, 2)

    if len(data['pos_pair']) == len(data['selected']):
        for i in range(len(data['pos_pair'])):
            data['pos_pair'][i] = float(f"{int(data['pos_pair'][i])}.{int(data['selected'][i])}")
            data['neg_pair'][i] = float(f"{int(data['neg_pair'][i])}.{int(data['selected'][i])}")

    max_val = max(max(data['neg_pair']), max(data['pos_pair']))

    im0 = ax[0].scatter(data['pos_pair'], data['neg_pair'], c=data['temp'], cmap=cm, marker='.')
    im1 = ax[1].scatter(data['pos_pair'], data['neg_pair'], c=cost,         cmap=cm, marker='.')

    ax[0].set_title('Temperature')
    ax[1].set_title('Cost (Norm. to initial. -1 if infeasible)')

    for i in range(2):
        ax[i].set_ylabel('Neg pair')
        ax[i].set_xlabel('Pos pair')
        ax[i].set_xlim(-0.5, max_val+0.5)
        ax[i].set_ylim(-0.5, max_val+0.5)
        ax[i].grid()

    fig.colorbar(im0, ax=ax[0])
    fig.colorbar(im1, ax=ax[1])
    fig.set_size_inches(14, 6)
    fig.savefig(f'{my_dir}/{name}_seqpair_scatter.png', dpi=300, pad_inches=0.001)
