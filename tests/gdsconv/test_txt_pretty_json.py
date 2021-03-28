import filecmp
import pathlib

from align.gdsconv.txt2prettyjson import convert_GDStxt_GDSprettyjson
from align.gdsconv.json2txt import convert_GDSjson_GDStxt

mydir = pathlib.Path(__file__).resolve().parent

def test_txt_pretty_json_roundtrip ():
    convert_GDStxt_GDSprettyjson (mydir / "file.txt", mydir / "fromtxt8.json")
    convert_GDSjson_GDStxt (mydir / "fromtxt8.json", mydir / "fromjson8.txt")
    assert (filecmp.cmp (mydir / "file.txt", mydir / "fromjson8.txt"))

def test_pretty_json_txt_roundtrip ():
    convert_GDSjson_GDStxt (mydir / "file.pretty.json", mydir / "fromjson9.txt")
    convert_GDStxt_GDSprettyjson (mydir / "fromjson9.txt", mydir / "fromtxt9.json")
    assert (filecmp.cmp (mydir / "file.pretty.json", mydir / "fromtxt9.json"))

