import filecmp
import pathlib

from align.gdsconv.gds2prettyjson import convert_GDS_GDSprettyjson
from align.gdsconv.json2gds import convert_GDSjson_GDS

mydir = pathlib.Path(__file__).resolve().parent

def test_gds_json_roundtrip ():
    convert_GDS_GDSprettyjson (mydir / "file.gds", mydir / "fromgds3.json")
    convert_GDSjson_GDS (mydir / "fromgds3.json", mydir / "fromjson3.gds")
    assert (filecmp.cmp (mydir / "file.gds", mydir / "fromjson3.gds"))

def test_json_gds_roundtrip ():
    convert_GDSjson_GDS (mydir / "file.pretty.json", mydir / "fromjson4.gds")
    convert_GDS_GDSprettyjson (mydir / "fromjson4.gds", mydir / "fromgds4.json")
    assert (filecmp.cmp (mydir / "file.pretty.json", mydir / "fromgds4.json"))

