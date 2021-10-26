import filecmp
import pathlib

from align.gdsconv.gds2json import convert_GDS_GDSjson
from align.gdsconv.json2gds import convert_GDSjson_GDS

mydir = pathlib.Path(__file__).resolve().parent

def test_gds_json_roundtrip ():
    convert_GDS_GDSjson (mydir / "file.gds", mydir / "fromgds1.json")
    convert_GDSjson_GDS (mydir / "fromgds1.json", mydir / "fromjson1.gds")
    assert (filecmp.cmp (mydir / "file.gds", mydir / "fromjson1.gds"))

    convert_GDS_GDSjson (mydir / "only_paths.gds", mydir / "only_paths_fromgds1.json")
    convert_GDSjson_GDS (mydir / "only_paths_fromgds1.json", mydir / "only_paths_fromjson1.gds")
    assert (filecmp.cmp (mydir / "only_paths.gds", mydir / "only_paths_fromjson1.gds"))

def test_json_gds_roundtrip ():
    convert_GDSjson_GDS (mydir / "file.json", mydir / "fromjson2.gds")
    convert_GDS_GDSjson (mydir / "fromjson2.gds", mydir / "fromgds2.json")
    assert (filecmp.cmp (mydir / "file.json", mydir / "fromgds2.json"))

    convert_GDSjson_GDS (mydir / "only_paths.json", mydir / "only_paths_fromjson2.gds")
    convert_GDS_GDSjson (mydir / "only_paths_fromjson2.gds", mydir / "only_paths_fromgds2.json")
    assert (filecmp.cmp (mydir / "only_paths.json", mydir / "only_paths_fromgds2.json"))
