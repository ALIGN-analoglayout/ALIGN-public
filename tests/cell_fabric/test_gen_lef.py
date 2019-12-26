import json
import align.cell_fabric.gen_lef as gen_lef
import datetime

import filecmp
import io
import pathlib

mydir = pathlib.Path(__file__).resolve().parent

def test_lef():

    block_name = "foo"
    json_file_name = mydir / "__json_diff_pair_cand"

    with open( json_file_name, "rt") as fp0, \
         open( mydir / "foo.lef_cand", 'wt') as fp1:
        gen_lef.gen_lef_json_fp( fp0, fp1, macro_name=block_name, cell_pin=['DA','DB','S'])

    assert filecmp.cmp( mydir / "foo.lef_cand", mydir / "foo.lef_gold")



