import json
import pathlib

def test_json_readable():
    with open(pathlib.Path(__file__).parent.parent.parent / "pdks" / "FinFET14nm_Mock_PDK" / "layers.json", "rt") as fp:
      j = json.load(fp)
