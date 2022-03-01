import os
import pytest
from align.schema import Model, Instance, SubCircuit, Library
from align.schema.types import set_context
import json


@pytest.fixture
def db():
    library = Library(loadbuiltins=False)
    with set_context(library):
        cmodel = Model(name="CAP", pins=["PLUS", "MINUS"], parameters={"VALUE": "5.0", "PARALLEL": 1})
        rmodel = Model(name="RES", pins=["PLUS", "MINUS"], parameters={"VALUE": "5.0", "PARALLEL": 1})
        model_nmos = Model(
            name="TESTMOS",
            pins=["D", "G", "S", "B"],
            parameters={"PARAM1": "1.0", "M": 1},
        )
        library.append(cmodel)
        library.append(rmodel)
        library.append(model_nmos)
        subckt = SubCircuit(
            name="SUBCKT", pins=["PLUS", "MINUS", "D", "G", "S", "B"], parameters=None
        )
        library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(
            Instance(
                name="C1",
                model="CAP",
                pins={"PLUS": "PLUS", "MINUS": "MINUS"},
                parameters={"VALUE": "2", "PARALLEL": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="R1",
                model="RES",
                pins={"PLUS": "PLUS", "MINUS": "MINUS"},
                parameters={"VALUE": "10", "PARALLEL": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M1",
                model="TESTMOS",
                pins={"D": "D", "G": "G", "S": "S", "B": "B"},
                parameters={"PARAM1": "1.0", "M": 1}
            )
        )
        subckt.elements.append(
            Instance(
                name="M2",
                model="TESTMOS",
                pins={"D": "D1", "G": "G1", "S": "S1", "B": "B"},
                parameters={"PARAM1": "1.0", "M": 2}
            )
        )
    return library


def write(lib):
    with open("sample.json", "w") as f:
        json.dump(lib.dict()["__root__"], f, indent=2)

def test_read(db):
    write(db)
    with open("sample.json", "r") as f:
        data = json.load(f)
    os.remove("sample.json")
    library = Library(loadbuiltins=False)
    with set_context(library):
        for x in data:
            if 'generator' in x:
                library.append(SubCircuit(**{k: v for k, v in x.items() if v}))
            else:
                library.append(Model(**{k:v for k,v in x.items() if v}))
    subckt = library.find("SUBCKT")
    assert subckt.get_element("C1").parameters == {"VALUE": "2", "PARALLEL": "1"}
    assert subckt.get_element("R1").parameters == {"VALUE": "10", "PARALLEL": "1"}
    assert subckt.get_element("M1").parameters == {"PARAM1": "1.0", "M": "1"}
    assert subckt.get_element("M2").parameters == {"PARAM1": "1.0", "M": "2"}
