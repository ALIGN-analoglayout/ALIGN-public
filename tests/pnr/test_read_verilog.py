import json
import pathlib
import io

from align import PnR
from align.pnr.toplevel import ReadVerilogJson, analyze_hN
from align.compiler.write_verilog_lef import write_verilog

mydir = pathlib.Path(__file__).resolve().parent

def test_A():
    DB = PnR.PnRdatabase()

    d = mydir / "current_mirror_ota_inputs"

    DB.ReadPDKJSON( str( d / "layers.json"))

    DB.ReadLEF( str( d / "current_mirror_ota.lef"))
    DB.ReadMap( str( d), "current_mirror_ota.map")

    assert DB.ReadVerilog( str(d), "current_mirror_ota.v", "current_mirror_ota")

    for hN in DB.hierTree:
        analyze_hN( "verilog", hN)

def test_B():
    d = mydir / "current_mirror_ota_inputs"

    with open( d / "current_mirror_ota.verilog.json", "rt") as fp:
        j = json.load( fp)

    with open( d / "current_mirror_ota.v", "rt") as fp:
        vstr = fp.read()

    with io.StringIO() as fp:
        write_verilog( j, fp)
        vvstr = fp.getvalue()
    
    # remove header and trailing spaces
    assert [ line.rstrip(' ') for line in vstr.split('\n')[4:]] == vvstr.split('\n')

def test_C():
    DB = PnR.PnRdatabase()

    d = mydir / "current_mirror_ota_inputs"

    DB.ReadPDKJSON( str( d / "layers.json"))

    DB.ReadLEF( str( d / "current_mirror_ota.lef"))
    DB.ReadMap( str( d), "current_mirror_ota.map")

    with open( d / "current_mirror_ota.verilog.json", "rt") as fp:
        j = json.load( fp)

    with open( d / "current_mirror_ota.verilog.v", "wt") as fp:
        write_verilog( j, fp)


    DB.ReadVerilog( str(d), "current_mirror_ota.verilog.v", "current_mirror_ota")

    for hN in DB.hierTree:
        analyze_hN( "verilogJsonVerilog", hN)


def test_D():
    DB = PnR.PnRdatabase()

    d = mydir / "current_mirror_ota_inputs"

    DB.ReadPDKJSON( str( d / "layers.json"))

    DB.ReadLEF( str( d / "current_mirror_ota.lef"))
    DB.ReadMap( str( d), "current_mirror_ota.map")

    with open( d / "current_mirror_ota.verilog.json", "rt") as fp:
        j = json.load( fp)

    global_signals = ReadVerilogJson( DB, j)

    DB.attach_constraint_files( str(d))
    DB.semantic0( "current_mirror_ota")
    DB.semantic1( global_signals)
    DB.semantic2()

    for hN in DB.hierTree:
        analyze_hN( "verilogJson", hN)
    
