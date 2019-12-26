import filecmp

from gdsconv.gds2prettyjson import convert_GDS_GDSprettyjson
from gdsconv.json2gds import convert_GDSjson_GDS

def test_gds_json_roundtrip ():
    convert_GDS_GDSprettyjson ("tests/file.gds", "tests/fromgds.json")
    convert_GDSjson_GDS ("tests/fromgds.json", "tests/fromjson.gds")
    assert (filecmp.cmp ("tests/file.gds", "tests/fromjson.gds"))

def test_json_gds_roundtrip ():
    convert_GDSjson_GDS ("tests/file.pretty.json", "tests/fromjson2.gds")
    convert_GDS_GDSprettyjson ("tests/fromjson2.gds", "tests/fromgds2.json")
    assert (filecmp.cmp ("tests/file.pretty.json", "tests/fromgds2.json"))

