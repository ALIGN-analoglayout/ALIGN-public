
import json
import cell_fabric.gen_gds_json
import datetime

import gdsconv.json2gds
import filecmp
import io
import pytest

@pytest.fixture
def setup():
    gds_layer_map = {"polycon" : 1,
                     "fin" : 2,
                     "poly" : 3,
                     "active" : 4,
                     "nselect" : 5,
                     "pselect" : 6,
                     "M0"   : 10,
                     "via0" : 11,
                     "M1"   : 12,
                     "via1" : 13,
                     "M2"   : 14,
                     "via2" : 15,
                     "M3"   : 16,
                     "bbox" : 50}
    via_gen_tbl = {
        "via2": (
            "M3_M2_CDNS_543864435520",
            {
            "via2": [-640,-640,640,640],
            "M2": [-1440,-640,1440,640],
            "M3": [-640,-1440,640,1440]
            }
        ),
        "via1": (
            "M2_M1_CDNS_543864435521",
            {
            "via1": [-640,-640,640,640],
            "M1": [-640,-1440,640,1440],
            "M2": [-1440,-640,1440,640]
            }
        )
    }
    return (gds_layer_map, via_gen_tbl)

def test_one(setup):
    gds_layer_map, via_gen_tbl = setup

    block_name = "foo"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp0, \
         open( json_file_name + "_gds_cand", 'wt') as fp1:
        cell_fabric.gen_gds_json.translate( block_name, '', fp0, fp1, gds_layer_map, via_gen_tbl,
                                            datetime.datetime( 2019, 1, 1, 0, 0, 0))

    with open( json_file_name + "_gds_cand", "rt") as fp0, \
         open( json_file_name + "_gds_gold", "rt") as fp1:
        cand = json.load( fp0)
        gold = json.load( fp1)
        assert cand == gold

def test_gds(setup):
    gds_layer_map, via_gen_tbl = setup

    block_name = "foo"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp0, \
         open( json_file_name + "_gds_cand", 'wt') as fp1:
        cell_fabric.gen_gds_json.translate( block_name, '', fp0, fp1, gds_layer_map, via_gen_tbl,
                                            datetime.datetime( 2019, 1, 1, 0, 0, 0))

    with open( json_file_name + "_gds_cand", "rt") as fp0, \
         open( "tests/test_gds.gds", 'wb') as fp1:
        gdsconv.json2gds.convert_GDSjson_GDS_fps( fp0, fp1)

    assert filecmp.cmp( "tests/test_gds.gds", "tests/test_gds.gds_gold", shallow=False)

def test_gds_stringio(setup):
    gds_layer_map, via_gen_tbl = setup

    block_name = "foo"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp0, \
         io.StringIO() as fp1:
        cell_fabric.gen_gds_json.translate( block_name, '', fp0, fp1, gds_layer_map, via_gen_tbl,
                                            datetime.datetime( 2019, 1, 1, 0, 0, 0))
        contents = fp1.getvalue()

    with io.StringIO( contents) as fp0, \
         open( "tests/test_gds.gds", 'wb') as fp1:
        gdsconv.json2gds.convert_GDSjson_GDS_fps( fp0, fp1)

    assert filecmp.cmp( "tests/test_gds.gds", "tests/test_gds.gds_gold", shallow=False)

