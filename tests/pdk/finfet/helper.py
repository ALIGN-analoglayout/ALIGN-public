import os
import json
import pathlib
from copy import deepcopy
import shutil
import align.pdk.finfet

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
    except:
        t = 'debug_run'
    return t


def comparator(name):
    netlist = f""".subckt {name} clk vcc_0p9 vin vip von vop vssx
mmp8 vip_d clk vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=1 nf=2
mmp5 vin_o vip_o vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=5 nf=2
mmp14 vop vip_o vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=1 nf=2
mmp10 vip_o clk vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=2 nf=2
mmp13 von vin_o vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=1 nf=2
mmp7 vin_d clk vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=1 nf=2
mmp9 vin_o clk vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=2 nf=2
mmp6 vip_o vin_o vcc_0p9 vcc_0p9 p w=360e-9 l=40e-9 m=5 nf=2
mmn0 vcom clk vssx vssx n w=2.88e-6 l=40e-9 m=1 nf=16
mmn11 von vin_o vssx vssx n w=360e-9 l=40e-9 m=1 nf=2
mmn12 vop vip_o vssx vssx n w=360e-9 l=40e-9 m=1 nf=2
mmn2 vip_d vip vcom vssx n w=360e-9 l=40e-9 m=18 nf=2
mmn3 vin_o vip_o vin_d vssx n w=360e-9 l=40e-9 m=8 nf=2
mmn4 vip_o vin_o vip_d vssx n w=360e-9 l=40e-9 m=8 nf=2
mmn1 vin_d vin vcom vssx n w=360e-9 l=40e-9 m=18 nf=2
.ends {name}
"""
    netlist_setup = f"""POWER = vcc_0p9
GND = vssx
"""
    return netlist, netlist_setup


def build_example(work_dir, name, netlist, netlist_setup, constraints):
    example = work_dir / name
    if example.exists() and example.is_dir():
        shutil.rmtree(example)
    example.mkdir(parents=True)
    with open(example / f'{name}.sp' ,'w') as fp:
        fp.write(netlist)
    with open(example / f'{name}.setup' ,'w') as fp:
        fp.write(netlist_setup)
    with open(example / f'{name}.const.json' ,'w') as fp:
        fp.write(constraints)    
    return example


def run_example(example, n=8, cleanup=True):
    run_dir = my_dir / f'run_{example.name}'
    if run_dir.exists() and run_dir.is_dir():
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True)
    os.chdir(run_dir)

    args = [str(example), '-p', str(pdk_dir), '-l','INFO', '-n', str(n)]
    results = align.CmdlineParser().parse_args(args)
    assert results is not None, f"{example.name}: No results generated"
    
    shutil.rmtree(run_dir)
    shutil.rmtree(example)
