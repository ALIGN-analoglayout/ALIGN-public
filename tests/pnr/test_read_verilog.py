import json
import pathlib

from align import PnR

mydir = pathlib.Path(__file__).resolve().parent

def test_A():
    DB = PnR.PnRdatabase()

    d = mydir / "current_mirror_ota_inputs"

    DB.ReadPDKJSON( str( d / "layers.json"))

    DB.ReadLEF( str( d / "current_mirror_ota.lef"))
    DB.ReadMap( str( d), "current_mirror_ota.map")

    DB.ReadVerilog( str(d), "current_mirror_ota.v", "current_mirror_ota")
