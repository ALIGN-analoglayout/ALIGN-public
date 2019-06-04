
import json
import cell_fabric.gen_gds_json

def test_one():
    
    block_name = "foo"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp, \
         open( json_file_name + "_gds_cand", 'wt') as ofile:
        cell_fabric.gen_gds_json.translate( block_name, '', fp, ofile, [0,0,0,0,0,0])

    with open( json_file_name + "_gds_cand", "rt") as fp0, \
         open( json_file_name + "_gds_gold", "rt") as fp1:
        cand = json.load( fp0)
        gold = json.load( fp1)
        assert cand == gold

    
