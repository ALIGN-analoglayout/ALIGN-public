import os
import json
import pathlib
from align.pdk.finfet import MOSGenerator

my_dir = pathlib.Path(__file__).resolve().parent

align_home = os.getenv('ALIGN_HOME')


def test_array_one():
    c = MOSGenerator()
    ports = {'SA': [('M1', 'S')], 'DA': [('M1', 'D')], 'GA': [('M1', 'G')]}
    parameters = {'m': 4, 'nf': 2, 'real_inst_type': 'n'}
    c.addNMOSArray(None, 2, 1, None, ports, **parameters)

    data = {'bbox': c.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c.removeDuplicates(allow_opens=True)}

    fn = "test_transistor_array_1"
    if align_home:
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2


def test_array_two():
    c = MOSGenerator()
    ports = {'S': [('M1', 'S'), ('M2', 'S')],
             'DA': [('M1', 'D')], 'DB': [('M2', 'D')],
             'GA': [('M1', 'G')], 'GB': [('M2', 'G')]
             }
    parameters = {'m': 4, 'stack': 4, 'real_inst_type': 'n'}
    c.addNMOSArray(None, 1, 1, None, ports, **parameters)
    
    data = {'bbox': c.bbox.toList(), 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': c.removeDuplicates(allow_opens=True)}

    fn = "test_transistor_array_2"
    if align_home:
        with open(pathlib.Path(align_home)/'Viewer'/'INPUT'/f'{fn}.json', "wt") as fp:
            fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_cand.json"), "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    with open(my_dir / (fn + "_gold.json"), "rt") as fp:
        data2 = json.load(fp)

    assert data == data2
