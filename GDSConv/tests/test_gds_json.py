import pytest
import filecmp

from gdsconv.txt2json import convert_GDStxt_GDSjson
from gdsconv.json2txt import convert_GDSjson_GDStxt
from gdsconv.gds2json import convert_GDS_GDSjson
from gdsconv.json2gds import convert_GDSjson_GDS

def test_gds_json_roundtrip ():
    convert_GDS_GDSjson ("tests/file.gds", "tests/fromgds.json")
    convert_GDSjson_GDS ("tests/fromgds.json", "tests/fromjson.gds")
    assert (filecmp.cmp ("tests/file.gds", "tests/fromjson.gds"))

def test_json_gds_roundtrip ():
    convert_GDSjson_GDS ("tests/file.json", "tests/fromjson2.gds")
    convert_GDS_GDSjson ("tests/fromjson2.gds", "tests/fromgds2.json")
    assert (filecmp.cmp ("tests/file.json", "tests/fromgds2.json"))

