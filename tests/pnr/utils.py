import os
import json
import pathlib
import shutil
import align.pdk.finfet
from align.cell_fabric import gen_lef

ALIGN_HOME = os.getenv('ALIGN_HOME')

MY_DIR = pathlib.Path(__file__).resolve().parent


def get_test_id():
    try:
        t = os.environ.get('PYTEST_CURRENT_TEST')
        t = t.split(' ')[0].split(':')[-1]
        t = t.replace('[', '_').replace(']', '').replace('-', '_')
        t = t[5:]
    except BaseException:
        t = 'debug'
    return t


def run_postamble(nm, cv, max_errors=0):

    if cv.bbox is None:
        cv.computeBbox()
    bbox = cv.bbox.toList()
    terminals = cv.removeDuplicates(silence_errors=True)

    # === Export problem to viewer
    data = {'bbox': bbox, 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': terminals}
    with open(pathlib.Path(ALIGN_HOME)/'Viewer'/'INPUT'/f'{nm.upper()}.json', "wt") as fp:
        fp.write(json.dumps(data, indent=2) + '\n')

    # === Find connected entities and generate a formal actual map

    def find_update_term(terminals, layer, rect, new_name):
        for term in terminals:
            if term['layer'] == layer and term['rect'] == rect:
                term['netName'] = new_name
                term['netType'] = 'pin'

    counters = {}
    fa_map = list()
    for net_opens in cv.rd.opens:
        actual = net_opens[0]
        for open_group in net_opens[1]:
            if actual not in counters:
                counters[actual] = 0
            counters[actual] += 1
            formal = actual + '__' + str(counters[actual])
            for term in open_group:
                find_update_term(terminals, term[0], term[1], formal)
            fa_map.append({'formal': formal, 'actual': actual})

    # === Generate top-level netlist
    ctn = 'leaf'

    instance = {'instance_name': 'ILEAF', 'abstract_template_name': ctn, 'fa_map': fa_map}

    topmodule = {'name': nm.upper(), 'parameters': [], 'instances': [instance], 'constraints': []}

    run_dir = MY_DIR / nm
    if run_dir.exists():
        assert run_dir.is_dir()
        shutil.rmtree(run_dir)
    run_dir.mkdir(parents=True, exist_ok=False)

    (run_dir / '1_topology').mkdir(parents=False, exist_ok=False)
    (run_dir / '2_primitives').mkdir(parents=False, exist_ok=False)

    with (run_dir / '1_topology' / f'{nm.upper()}.verilog.json').open('wt') as fp:
        verilog_d = {'modules': [topmodule], 'global_signals': []}
        json.dump(verilog_d, fp=fp, indent=2)

    with (run_dir / '1_topology' / '__primitives_library__.json').open('wt') as fp:
        primitives_library = [{'name': ctn, 'pins': ['INP', 'OUT'], 'generator': {'name': ctn}}]
        json.dump(primitives_library, fp=fp, indent=2)

    with (run_dir / '2_primitives' / '__primitives__.json').open('wt') as fp:
        primitives_d = {ctn: {'abstract_template_name': ctn, 'concrete_template_name': ctn}}
        json.dump(primitives_d, fp=fp, indent=2)

    terminals.append({"layer": "Nwell", "netName": None, "rect": bbox, "netType": "drawing"})

    with (run_dir / '2_primitives' / f'{ctn}.json').open('wt') as fp:
        layout_d = {'bbox': bbox, 'globalRoutes': [], 'globalRouteGrid': [], 'terminals': terminals}
        json.dump(layout_d, fp=fp, indent=2)

    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn, bodyswitch=1, blockM=0, p=cv.pdk, mode='placement')
    gen_lef.json_lef(run_dir / '2_primitives' / f'{ctn}.json', ctn, bodyswitch=1, blockM=0, p=cv.pdk)

    os.chdir(run_dir)

    args = ['unknown', '-s', nm, '--flow_start', '3_pnr', '--skipGDS', '-p', str(cv.pdk.layerfile.parent)]
    results = align.CmdlineParser().parse_args(args)
    assert results is not None, f'No results for {nm}'

    for result in results:
        _, variants = result
        for (k, v) in variants.items():
            assert 'errors' in v, f"No Layouts were generated for {nm} ({k})"
            assert v['errors'] <= max_errors, f"{nm} ({k}):Number of DRC errors: {str(v['errors'])}"
