import json

def test_json_readable():
    with open("FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json","rt") as fp:
      j = json.load(fp)
