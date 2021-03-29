import filecmp
import pathlib

from align.gdsconv.txt2prettyjson import convert_GDStxt_GDSprettyjson
from align.gdsconv.json2txt import convert_GDSjson_GDStxt

mydir = pathlib.Path(__file__).resolve().parent

def test_txt_pretty_json_roundtrip ():
    convert_GDStxt_GDSprettyjson (mydir / "file.txt", mydir / "fromtxt9.json")
    convert_GDSjson_GDStxt (mydir / "fromtxt9.json", mydir / "fromjson9.txt")
    assert (filecmp.cmp (mydir / "file.txt", mydir / "fromjson9.txt"))

def test_pretty_json_txt_roundtrip ():
    convert_GDSjson_GDStxt (mydir / "file.pretty.json", mydir / "fromjson10.txt")
    convert_GDStxt_GDSprettyjson (mydir / "fromjson10.txt", mydir / "fromtxt10.json")
    assert (filecmp.cmp (mydir / "file.pretty.json", mydir / "fromtxt10.json"))

