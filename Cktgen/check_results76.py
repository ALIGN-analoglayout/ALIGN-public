
import json
import re
import argparse

from align.cell_fabric import transformation
from intel_p1276p31.canvas import IntelP1276p31canvas


def check_results(ckt_name):

    ckt_name_json = ckt_name
    if not ckt_name.endswith('.json'):
        ckt_name_json += '.json'

    with open( ckt_name_json, "rt") as fp:
        d = json.load(fp)

    layers = [f'M{k}' for k in range(7)] + [f'V{k}' for k in range(6)]

    p = re.compile("^(.*)_gr$")

    terminals = []
    for term in d['terminals']:
        if term['layer'] not in layers:
            continue
        nm = term['netName']
        if nm is not None and p.match(nm):
            continue
        # # !kor and !float signals might be need. Right now, just excluding them.
        # if nm in ['!kor', '!float']: continue
        terminals.append(term)
    d['terminals'] = terminals

    cnv = IntelP1276p31canvas()
    cnv.bbox = transformation.Rect(*d['bbox'])
    cnv.terminals = d['terminals']

    # data = cnv.gen_data(run_pex=True, run_drc=True, postprocess=True)

    with open(ckt_name + "_prim.json", "w") as fp:
        data = cnv.writeJSON(fp, postprocess=True)

    return data


if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check <circuit>.JSON against design rules")
    parser.add_argument("--circuit", required=True, type=str, help="Circuit name")
    args = parser.parse_args()
    check_results(args.circuit)
