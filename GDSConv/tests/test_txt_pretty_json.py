import filecmp

from gdsconv.txt2prettyjson import convert_GDStxt_GDSprettyjson
from gdsconv.json2txt import convert_GDSjson_GDStxt

def test_txt_pretty_json_roundtrip ():
    convert_GDStxt_GDSprettyjson ("tests/file.txt", "tests/fromtxt.json")
    convert_GDSjson_GDStxt ("tests/fromtxt.json", "tests/fromjson.txt")
    assert (filecmp.cmp ("tests/file.txt", "tests/fromjson.txt"))

def test_pretty_json_txt_roundtrip ():
    convert_GDSjson_GDStxt ("tests/file.pretty.json", "tests/fromjson.txt")
    convert_GDStxt_GDSprettyjson ("tests/fromjson.txt", "tests/fromtxt.json")
    assert (filecmp.cmp ("tests/file.pretty.json", "tests/fromtxt.json"))

