import argparse
import datetime
from cell_fabric import gen_gds_json, Pdk, pdk
import json
import gdsconv.json2gds
import filecmp
import io
import pytest
#from pathlib import Path

#pdkfile = (Path(__file__).parent / 'layers.json').resolve()
pdkfile = '../PDK_Abstraction/FinFET14nm_Mock_PDK/layers.json'
p = pdk.Pdk().load(pdkfile)
via_gen_tbl = p.get_via_table()


@pytest.fixture

def test_one():
    block_name = "__json_cmc_nmos_big_no_duplicates_gds_cand"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp0, \
         open( json_file_name + "_gds_cand", 'wt') as fp1:
        gen_gds_json.translate(  block_name, '', pdkfile, 0, fp0, fp1, via_gen_tbl,
                                            datetime.datetime( 2019, 1, 1, 0, 0, 0))

    with open( json_file_name + "_gds_cand", "rt") as fp0, \
         open( json_file_name + "_gds_gold", "rt") as fp1:
        cand = json.load( fp0)
        gold = json.load( fp1)
        assert cand == gold

def test_gds():

    block_name = "__json_cmc_nmos_big_no_duplicates_gds_cand"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp0, \
         open( json_file_name + "_gds_cand", 'wt') as fp1:
        gen_gds_json.translate(  block_name, '', pdkfile, 0, fp0, fp1, via_gen_tbl,
                                            datetime.datetime( 2019, 1, 1, 0, 0, 0))

    with open( json_file_name + "_gds_cand", "rt") as fp0, \
         open( "tests/test_gds.gds", 'wb') as fp1:
        gdsconv.json2gds.convert_GDSjson_GDS_fps( fp0, fp1)

    assert filecmp.cmp( "tests/test_gds.gds", "tests/test_gds.gds_gold", shallow=False)

def test_gds_stringio():

    block_name = "__json_cmc_nmos_big_no_duplicates_gds_cand"
    json_file_name = "tests/__json_cmc_nmos_big_no_duplicates"

    with open( json_file_name + "_cand", "rt") as fp0, \
         io.StringIO() as fp1:
        gen_gds_json.translate( block_name, '', pdkfile, 0, fp0, fp1, via_gen_tbl,
                                            datetime.datetime( 2019, 1, 1, 0, 0, 0))
        contents = fp1.getvalue()

    with io.StringIO( contents) as fp0, \
         open( "tests/test_gds.gds", 'wb') as fp1:
        gdsconv.json2gds.convert_GDSjson_GDS_fps( fp0, fp1)

    assert filecmp.cmp( "tests/test_gds.gds", "tests/test_gds.gds_gold", shallow=False)

