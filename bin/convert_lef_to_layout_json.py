import pathlib
import json
import os
import argparse

from align.cell_fabric import pdk, lef_to_json

align_home = os.environ.get( 'ALIGN_HOME', None)

parser = argparse.ArgumentParser(description="Generate layout json files from LEF.")

parser.add_argument("-p",
                    "--pdk_dir",
                    type=str,
                    required=align_home is None,
                    default=None if align_home is None else align_home + '/pdks/FinFET14nm_Mock_PDK',
                    help='Path to PDK directory')

parser.add_argument("-n",
                    "--nm",
                    type=str,
                    help='Name of LEF file to convert')

args = parser.parse_args()


pdkdir = pathlib.Path(args.pdk_dir)

p = pdk.Pdk().load(pdkdir / 'layers.json')

with open(p.layerfile, "rt") as fp1:
    j1 = json.load(fp1)
scale_factor = j1["ScaleFactor"]

m1pitch = p['M1']['Pitch']
m2pitch = p['M2']['Pitch']

nm = args.nm

with open(f'{nm}.lef', 'rt') as fp:
    lef_txt = fp.read()

new_layout_d = lef_to_json.lef_txt_to_layout_d( lef_txt, nm, scale_factor=scale_factor, m1pitch=m1pitch, m2pitch=m2pitch)

with open(f'{nm}.json', 'wt') as fp:
    json.dump( new_layout_d, fp=fp, indent=2)
