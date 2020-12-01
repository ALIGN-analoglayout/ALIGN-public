
import json
import pathlib
import re
import argparse
from pprint import pformat

from align.cell_fabric import transformation

from intel_p1276p31.canvas import IntelP1276p31canvas

def check_results(ckt_name, skip_layers=None):

    ckt_name_json = ckt_name
    if not ckt_name.endswith('.json'):
        ckt_name_json += '.json'

    with open( ckt_name_json, "rt") as fp:
        d = json.load(fp)

    if skip_layers is None:
        skip_layers = set( ["boundary", "diearea", "cellarea", "ndiff", "pdiff", "nwell", "poly", "gcn", "tcn", "polycon", "diffcon"])
    else:
        skip_layers = set( ["boundary", "diearea", "cellarea"])

    layer_tbl = {
                  "metal0": "M0",
                  "metal1": "M1",
                  "metal2": "M2",
                  "metal3": "M3",
                  "metal4": "M4",
                  "metal5": "M5",
                  "via0": "V0",
                  "via1": "V1",
                  "via2": "V2",
                  "via3": "V3",
                  "via4": "V4"}

    p = re.compile( "^(.*)_gr$")

    terminals = []
    for term in d['terminals']:
        ly = term['layer']
        if str(ly).lower() not in layer_tbl: continue
        nm = term['netName'] if 'netName' in term else term['net_name']
        # #
        # # !kor and !float signals might be need. Right now, just excluding them.
        # #
        # if nm in ['!kor', '!float']: continue
        if nm is not None and p.match(nm): continue
        term['layer'] = layer_tbl.get( ly, ly)
        terminals.append( term)
    d['terminals'] = terminals

    cnv = IntelP1276p31canvas()

    cnv.bbox = transformation.Rect( *d['bbox'])
    cnv.terminals = d['terminals']

    data = cnv.gen_data(run_pex=True, run_drc=True)

    with open( ckt_name + "_prim.json", "w") as fp:
        cnv.writeJSON(fp)

    return(data)

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Check <circuit>.JSON against design rules")
    parser.add_argument("--circuit", required=True, type=str, help="Circuit name")

    args = parser.parse_args()

    check_results(args.circuit)
