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

verilog_json = """\
{
    "modules" : [
	{
	    "name": "current_mirror_ota",
	    "parameters": ["id", "vbiasnd", "vinn", "vinp", "voutp"],
	    "instances": [
		{
		    "template_name": "DCL_PMOS_nfin60_n12_X5_Y1_RVT",
		    "instance_name": "m21",
		    "fa_map": [
			{ "formal": "D", "actual": "net16"},
			{ "formal": "S", "actual": "vdd"}
		    ]
		},
		{
		    "template_name": "Switch_PMOS_nfin240_n12_X5_Y4_ST2_RVT",
		    "instance_name": "m20s",
		    "fa_map": [
			{ "formal": "D", "actual": "vbiasnd"},
			{ "formal": "G", "actual": "net16"},
			{ "formal": "S", "actual": "vdd"}
		    ]
		},
		{
		    "template_name": "DCL_PMOS_nfin60_n12_X5_Y1_RVT",
		    "instance_name": "m19",
		    "fa_map": [
			{ "formal": "D", "actual": "net27"},
			{ "formal": "S", "actual": "vdd"}
		    ]
		},
		{
		    "template_name": "Switch_PMOS_nfin240_n12_X5_Y4_ST2_RVT",
		    "instance_name": "m18s",
		    "fa_map": [
			{ "formal": "D", "actual": "voutp"},
			{ "formal": "G", "actual": "net27"},
			{ "formal": "S", "actual": "vdd"}
		    ]
		},
		{
		    "template_name": "SCM_NMOS_nfin10_n12_X1_Y1_RVT",
		    "instance_name": "m14_m16",
		    "fa_map": [
			{ "formal": "DA", "actual": "id"},
			{ "formal": "DB", "actual": "net24"},
			{ "formal": "S", "actual": "vss"}
		    ]
		},
		{
		    "template_name": "SCM_NMOS_nfin24_n12_X2_Y1_RVT",
		    "instance_name": "m11_m10",
		    "fa_map": [
			{ "formal": "DA", "actual": "vbiasnd"},
			{ "formal": "DB", "actual": "voutp"},
			{ "formal": "S", "actual": "vss"}
		    ]
		},
		{
		    "template_name": "DP_NMOS_B_nfin28_n12_X3_Y1_RVT",
		    "instance_name": "m17_m15",
		    "fa_map": [
			{ "formal": "B", "actual": "vss"},
			{ "formal": "DA", "actual": "net16"},
			{ "formal": "DB", "actual": "net27"},
			{ "formal": "GA", "actual": "vinn"},
			{ "formal": "GB", "actual": "vinp"},
			{ "formal": "S", "actual": "net24"}
		    ]
		}
	    ]
	}
    ],
    "celldefines": [
	{
	    "name": "global_power",
	    "supply0": "vss",
	    "supply1": "vdd"
	}
    ]
}
"""

def test_B():
    d = mydir / "current_mirror_ota_inputs"

    with io.StringIO( verilog_json) as fp:
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

    with io.StringIO( verilog_json) as fp:
        j = json.load( fp)

    with open( d / "current_mirror_ota.verilog.v", "wt") as fp:
        write_verilog( j, fp)


    DB.ReadVerilog( str(d), "current_mirror_ota.verilog.v", "current_mirror_ota")

    
