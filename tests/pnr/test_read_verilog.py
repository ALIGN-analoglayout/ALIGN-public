import json
import pathlib
import io

from align import PnR

mydir = pathlib.Path(__file__).resolve().parent

def test_A():
    DB = PnR.PnRdatabase()

    d = mydir / "current_mirror_ota_inputs"

    DB.ReadPDKJSON( str( d / "layers.json"))

    DB.ReadLEF( str( d / "current_mirror_ota.lef"))
    DB.ReadMap( str( d), "current_mirror_ota.map")

    DB.ReadVerilog( str(d), "current_mirror_ota.v", "current_mirror_ota")

def write_verilog( j, ofp):

    for module in j['modules']:
        print( f"module {module['name']} ( {', '.join( module['parameters'])} );", file=ofp) 
        print( f"input {', '.join( module['parameters'])};", file=ofp) 
        print( file=ofp)
        for instance in module['instances']:
            pl = ', '.join( f".{fa['formal']}({fa['actual']})" for fa in instance['fa_map'])
            print( f"{instance['template_name']} {instance['instance_name']} ( {pl} );", file=ofp)

        print( file=ofp)
        print( 'endmodule', file=ofp)
        
    if 'celldefines' in j:
        print( file=ofp)
        print( "`celldefine", file=ofp)
        for cd in j['celldefines']:
            txt = f'''\
module {cd['name']};
supply0 {cd['supply0']};
supply1 {cd['supply1']};
endmodule'''
            print( txt, file=ofp)
        print( "`endcelldefine", file=ofp)

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

    
