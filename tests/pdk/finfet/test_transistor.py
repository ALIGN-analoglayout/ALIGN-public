import os
import json
import pathlib
from align.pdk.finfet import CanvasPDK, mos, tap
from align.schema.transistor import Transistor

my_dir = pathlib.Path(__file__).resolve().parent


def test_one():
    tx = Transistor(model_name='n', nf=2, nfin=4, device_type='stack')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    data['globalRoutes'] = data['globalRouteGrid'] = []

    fn = "test_transistor_1"

    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)
        
    assert data == data2


def test_two():
    tx = Transistor(model_name='n', nf=4, nfin=4, device_type='stack')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    data['globalRoutes'] = data['globalRouteGrid'] = []

    fn = "test_transistor_2"
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_three():
    tx = Transistor(model_name='n', nf=2, nfin=4, device_type='parallel')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    data['globalRoutes'] = data['globalRouteGrid'] = []

    fn = "test_transistor_3"
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)
        
    assert data == data2


def test_four():
    tx = Transistor(model_name='n', nf=4, nfin=4, device_type='parallel')
    data = mos(CanvasPDK, tx, track_pattern={'G':[6], 'D':[4], 'S':[2]})
    data['globalRoutes'] = data['globalRouteGrid'] = []

    fn = "test_transistor_4"
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_five():
    tx = Transistor(model_name='n', nf=2, nfin=4, device_type='stack')
    data = tap(CanvasPDK, tx)
    data['globalRoutes'] = data['globalRouteGrid'] = []

    fn = "test_transistor_5"
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_six():
    tx = Transistor(model_name='n', nf=4, nfin=4, device_type='stack')
    data = tap(CanvasPDK, tx)
    data['globalRoutes'] = data['globalRouteGrid'] = []

    fn = "test_transistor_6"
    if align_home := os.getenv('ALIGN_HOME'):
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2
