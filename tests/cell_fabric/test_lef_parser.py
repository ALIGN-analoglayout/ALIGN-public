
from align.cell_fabric import lef_parser
from align.cell_fabric import lef_to_json

def test_A():
    with open( "tests/cell_fabric/__lef_flash_adc_3bit", "rt") as fp:
        txt = fp.read()
        p = lef_parser.LEFParser()
        p.parse(txt)

        
        tbl = {}
        for macro in p.macros:
            assert macro.macroName not in tbl
            tbl[macro.macroName] = macro

        assert 'Res_4200' in tbl
        assert 'Res_8000' in tbl
        assert 'CMC_PMOS_S_n12_X1_Y1' in tbl

        assert len(tbl) == 12

def test_B():
    with open( "tests/cell_fabric/__lef_capacitor", "rt") as fp:
        txt = fp.read()
        p = lef_parser.LEFParser()
        p.parse(txt)

        
        tbl = {}
        for macro in p.macros:
            assert macro.macroName not in tbl
            tbl[macro.macroName] = macro

        assert 'cap_12f' in tbl

        assert len(tbl) == 1

def test_C():
    lef_to_json.lef_to_json( "tests/cell_fabric/__lef_capacitor")
