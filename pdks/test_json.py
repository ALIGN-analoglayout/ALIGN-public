import json
import pathlib

def test_json_readable():
    with open(pathlib.Path(__file__).parent / "FinFET14nm_Mock_PDK" / "layers.json", "rt") as fp:
      j = json.load(fp)
