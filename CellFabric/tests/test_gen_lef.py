import json
import cell_fabric.gen_lef
import datetime

import filecmp
import io

def test_lef():
    
    
    block_name = "foo"
    json_file_name = "tests/__json_diff_pair"

    with open( json_file_name + "_cand", "rt") as fp0, \
         open( "tests/foo.lef_cand", 'wt') as fp1:
        cell_fabric.gen_lef.gen_lef_json_fp( fp0, fp1, macro_name=block_name, cell_pin=['G','DA','DB','SA','SB'])

    assert filecmp.cmp( "tests/foo.lef_cand", "tests/foo.lef_gold")



