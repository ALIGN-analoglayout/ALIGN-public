
import json
import pathlib
import re
import argparse

from align.cell_fabric.gen_gds_json import translate_data
from align.cell_fabric import pdk

if __name__ == "__main__":

    parser = argparse.ArgumentParser(description="Converts <circuit>.JSON to <circuit>.GDS")
    parser.add_argument("--circuit", required=True, type=str, help="Circuit name")

    args = parser.parse_args()

    ckt_name = args.circuit

    print('Converting ', ckt_name)

    with open( ckt_name + ".json", "rt") as fp:
        d = json.load(fp)

    skip_layers = set( ["boundary", "diearea", "cellarea"])

    layer_tbl = { "poly": "Poly",
                  "diffcon": "Diffcon",
                  "polycon": "Polycon",
                  "nwell": "Nwell",
                  "pdiff": "Pdiff",
                  "ndiff": "Ndiff",
                  "metal1": "M1",
                  "metal2": "M2",
                  "metal3": "M3",
                  "metal4": "M4",
                  "metal5": "M5",
                  "via0": "V0",
                  "via1": "V1",
                  "via2": "V2",
                  "via3": "V3",
                  "via4": "V4",
                  "basepitchid": "BasepitchID",
                  "devtype1id": "DEVTYPE1ID",
                  "devtype2id": "DEVTYPE2ID",
                  "devflavn1id": "Devflavn1id",
                  "devflavp1id": "Devflavp1id",
                  "devflavn4id": "Devflavn4id",
                  "devflavp4id": "Devflavp4id",
                  "tcn": "Diffcon",
                  "gcn": "Polycon"
                  }


    terminals = []
    for term in d['terminals']:
        ly = term['layer']
        if ly in skip_layers: continue
        term['layer'] = layer_tbl.get( ly, ly)
        terminals.append( term)
    d['terminals'] = terminals

    pdkfile = pathlib.Path('Intel/intel_p1222p2/layers.json')
    p = pdk.Pdk().load(pdkfile)

    exclude_pattern = re.compile( r'^.*_gr$')

    dd = translate_data( ckt_name, exclude_pattern, p.layerfile, 1, d, p.get_via_table()) 

    with open( ckt_name + ".gds.json", "wt") as fp:
        json.dump( dd, fp=fp, indent=2)
