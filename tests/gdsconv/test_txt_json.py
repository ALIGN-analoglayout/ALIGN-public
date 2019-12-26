import filecmp
import pathlib

from align.gdsconv.txt2json import convert_GDStxt_GDSjson
from align.gdsconv.json2txt import convert_GDSjson_GDStxt

mydir = pathlib.Path(__file__).resolve().parent

def test_txt_json_roundtrip ():
    convert_GDStxt_GDSjson (mydir / "file.txt", mydir / "fromtxt.json")
    convert_GDSjson_GDStxt (mydir / "fromtxt.json", mydir / "fromjson.txt")
    assert (filecmp.cmp (mydir / "file.txt", mydir / "fromjson.txt"))

def test_json_txt_roundtrip ():
    convert_GDSjson_GDStxt (mydir / "file.json", mydir / "fromjson.txt")
    convert_GDStxt_GDSjson (mydir / "fromjson.txt", mydir / "fromtxt.json")
    assert (filecmp.cmp (mydir / "file.json", mydir / "fromtxt.json"))

