from align.cell_fabric import gen_lef, pdk

import filecmp
import pathlib

mydir = pathlib.Path(__file__).resolve().parent

pdkdir = pathlib.Path(__file__).parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK"

p = pdk.Pdk().load(pdkdir / 'layers.json')

def test_lef():

    block_name = "foo"
    json_file_name = mydir / "__json_diff_pair_cand_lef"

    with open( json_file_name, "rt") as fp0, \
         open( mydir / "foo.lef_cand", 'wt') as fp1:
        gen_lef.json_lef( json_file_name, 'foo_cand',
                          bodyswitch=0, blockM=0, p=p)

    assert filecmp.cmp( mydir / "foo_cand.lef", mydir / "foo.lef_gold")



