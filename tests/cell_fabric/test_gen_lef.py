import align.cell_fabric.gen_lef as gen_lef

import filecmp
import pathlib
import io

mydir = pathlib.Path(__file__).resolve().parent

def test_lef():

    block_name = "foo"
    json_file_name = mydir / "__json_diff_pair_cand"

    with open( json_file_name, "rt") as fp0, \
         open( mydir / "foo.lef_cand", 'wt') as fp1:
        gen_lef.gen_lef_json_fp( fp0, fp1, macro_name=block_name, cell_pin=['DA','DB','S'])

    assert filecmp.cmp( mydir / "foo.lef_cand", mydir / "foo.lef_gold")

def test_lef_nooffset():
    block_name = "foo"
    str_inp_json = """{
  "bbox": [
    0,
    0,
    1000,
    2000
  ],
  "globalRoutes": [],
  "globalRouteGrid": [],
  "terminals": []
}
"""
    str_gold_lef = """MACRO foo
  ORIGIN 0.0000 0.0000 ;
  FOREIGN foo 0 0 ;
  SIZE 0.1000 BY 0.2000 ;
  OBS
  END
END foo
"""

    with io.StringIO( str_inp_json) as fp0, \
         io.StringIO() as fp1:
        gen_lef.gen_lef_json_fp( fp0, fp1, macro_name=block_name, cell_pin=[])

        assert fp1.getvalue() == str_gold_lef

def test_lef_offset():
    block_name = "foo"
    str_inp_json = """{
  "bbox": [
    100,
    200,
    1100,
    2200
  ],
  "globalRoutes": [],
  "globalRouteGrid": [],
  "terminals": []
}
"""
    str_gold_lef = """MACRO foo
  ORIGIN 0.0100 0.0200 ;
  FOREIGN foo 0 0 ;
  SIZE 0.1000 BY 0.2000 ;
  OBS
  END
END foo
"""

    with io.StringIO( str_inp_json) as fp0, \
         io.StringIO() as fp1:
        gen_lef.gen_lef_json_fp( fp0, fp1, macro_name=block_name, cell_pin=[])

        assert fp1.getvalue() == str_gold_lef
