import filecmp

from gdsconv.txt2json import convert_GDStxt_GDSjson
from gdsconv.json2txt import convert_GDSjson_GDStxt

def test_txt_json_roundtrip ():
    convert_GDStxt_GDSjson ("tests/file.txt", "tests/fromtxt.json")
    convert_GDSjson_GDStxt ("tests/fromtxt.json", "tests/fromjson.txt")
    assert (filecmp.cmp ("tests/file.txt", "tests/fromjson.txt"))

def test_json_txt_roundtrip ():
    convert_GDSjson_GDStxt ("tests/file.json", "tests/fromjson.txt")
    convert_GDStxt_GDSjson ("tests/fromjson.txt", "tests/fromtxt.json")
    assert (filecmp.cmp ("tests/file.json", "tests/fromtxt.json"))

