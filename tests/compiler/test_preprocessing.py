import pytest
from align.schema import Model, Instance, SubCircuit, Library, constraint
from align.schema.types import set_context
from align.compiler.preprocess import (
    add_parallel_devices,
    add_series_devices,
    find_dummy_hier,
    remove_dummies,
    remove_dummy_devices,
    define_SD
)


@pytest.fixture
def db():
    library = Library(loadbuiltins=False)
    with set_context(library):
        cmodel = Model(name="CAP", pins=["PLUS", "MINUS"], parameters={"VALUE": "5.0", "PARALLEL": 1})
        rmodel = Model(name="RES", pins=["PLUS", "MINUS"], parameters={"VALUE": "5.0", "PARALLEL": 1})
        library.append(cmodel)
        library.append(rmodel)
        model_nmos = Model(
            name="TESTMOS",
            pins=["D", "G", "S", "B"],
            parameters={"PARAM1": "1.0", "M": 1, "PARAM2": "2", "PARALLEL": 1},
        )
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
                name="C2",
                model="CAP",
                pins={"PLUS": "PLUS", "MINUS": "MINUS"},
                parameters={"VALUE": "2", "PARALLEL": 1},
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
                name="R2",
                model="RES",
                pins={"PLUS": "PLUS", "MINUS": "MINUS"},
                parameters={"VALUE": "10", "PARALLEL": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="R3",
                model="RES",
                pins={"PLUS": "PLUS", "MINUS": "MINUS"},
                parameters={"VALUE": "10"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M1",
                model="TESTMOS",
                pins={"D": "D", "G": "G", "S": "S", "B": "B"},
                parameters={"PARAM1": "1.0", "M": 1, "PARAM2": "2"}
            )
        )
        subckt.elements.append(
            Instance(
                name="M2",
                model="TESTMOS",
                pins={"D": "D", "G": "G", "S": "S", "B": "B"},
                parameters={"PARAM1": "1.0", "M": 1, "PARAM2": "2"}
            )
        )

    return subckt


def test_parallel(db):

    assert db.get_element("C1").name == "C1"
    assert db.get_element("C1").parameters == {"VALUE": "2", "PARALLEL": "1"}
    add_parallel_devices(db)
    assert db.get_element("C1").parameters == {"VALUE": "2", "PARALLEL": "2"}
    assert db.get_element("C2") is None, 'C2 should have been removed'
    assert db.get_element("R1").parameters == {"VALUE": "10", "PARALLEL": "3"}
    assert db.get_element("R2") is None, 'R2 should have been removed'
    assert db.get_element("R3") is None, 'R3 should have been removed'
    assert db.get_element("M1").parameters == {
        "PARAM1": "1.0",
        "M": "1",
        "PARAM2": "2",
        "PARALLEL": "2",
    }
    assert db.get_element("M2") is None, 'Should M2 have been removed from the db as it has been merged to M1?'


@pytest.fixture
def dbs():
    library = Library(loadbuiltins=False)
    with set_context(library):
        cmodel = Model(name="CAP", pins=["PLUS", "MINUS"], parameters={"VALUE": "5.0", "STACK": 1})
        rmodel = Model(name="RES", pins=["PLUS", "MINUS"], parameters={"VALUE": "5.0", "STACK": 1})
        library.append(cmodel)
        library.append(rmodel)
        model_nmos = Model(
            name="TESTMOS",
            pins=["D", "G", "S", "B"],
            parameters={"PARAM1": "1.0", "M": 1, "PARAM2": "2", "STACK": 1},
        )
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
                pins={"PLUS": "PLUS", "MINUS": "netc1"},
                parameters={"VALUE": "2", "STACK": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="C2",
                model="CAP",
                pins={"PLUS": "netc1", "MINUS": "MINUS"},
                parameters={"VALUE": "2", "STACK": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="R1",
                model="RES",
                pins={"PLUS": "PLUS", "MINUS": "netr1"},
                parameters={"VALUE": "10", "STACK": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="R2",
                model="RES",
                pins={"PLUS": "netr1", "MINUS": "netr2"},
                parameters={"VALUE": "10", "STACK": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="R3",
                model="RES",
                pins={"PLUS": "netr2", "MINUS": "MINUS"},
                parameters={"VALUE": "10", "STACK": "1"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M1",
                model="TESTMOS",
                pins={"D": "D", "G": "G", "S": "netm1", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M2",
                model="TESTMOS",
                pins={"D": "netm1", "G": "G", "S": "S", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M3",
                model="TESTMOS",
                pins={"D": "D", "G": "G1", "S": "netm2", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M4",
                model="TESTMOS",
                pins={"D": "netm2", "G": "G1", "S": "netm3", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M5",
                model="TESTMOS",
                pins={"D": "netm3", "G": "G1", "S": "S", "B": "B"},
            )
        )

    return subckt


def test_series(dbs):
    assert dbs.get_element("C1").name == "C1"
    assert dbs.get_element("M1").parameters == {
        "PARAM1": "1.0",
        "M": "1",
        "PARAM2": "2",
        "STACK": "1"
    }
    add_series_devices(dbs)
    assert dbs.get_element("C1").parameters == {"VALUE": "2", "STACK": "2"}
    assert dbs.get_element("R1").parameters == {"VALUE": "10", "STACK": "3"}
    assert dbs.get_element("M1").parameters == {
        "PARAM1": "1.0",
        "M": "1",
        "PARAM2": "2",
        "STACK": "2",
    }
    assert dbs.get_element("M3").parameters == {
        "PARAM1": "1.0",
        "M": "1",
        "PARAM2": "2",
        "STACK": "3",
    }
    assert len(dbs.elements) == 4
    assert dbs.get_element("M2") is None, 'Should M2 have been removed from the db as it has been merged to M1?'
    assert dbs.get_element("M5") is None, 'Should M5 have been removed from the db as it has been merged to M3?'


@pytest.fixture
def dbr():
    library = Library()
    with set_context(library):
        model_nmos = Model(
            name="TESTMOS",
            pins=["D", "G", "S", "B"],
            parameters={"PARAM1": "1.0", "M": 1, "PARAM2": "2", "PARAM": 1},
        )
        library.append(model_nmos)
        leaf_subckt = SubCircuit(
            name="LEAF_CKT", pins=["LD", "LG", "LS", "LB"], parameters={"PARAM": 1}
        )
        library.append(leaf_subckt)
        trunk_subckt = SubCircuit(
            name="TRUNK_CKT", pins=["TD", "TG", "TS", "TB"], parameters={"PARAM": 1}
        )
        library.append(trunk_subckt)
        top_subckt = SubCircuit(
            name="TOP_CKT", pins=["D", "G", "S", "B"], parameters={"PARAM": 1}
        )
        library.append(top_subckt)
    with set_context(leaf_subckt.elements):
        leaf_subckt.elements.append(
            Instance(
                name="M1",
                model="TESTMOS",
                pins={"D": "LD", "G": "LG", "S": "LS", "B": "LB"},
            )
        )
    with set_context(trunk_subckt.elements):
        trunk_subckt.elements.append(
            Instance(
                name="XTR1",
                model="LEAF_CKT",
                pins={"LD": "TD", "LG": "TG", "LS": "TS", "LB": "TB"},
                parameters={"PARAM": 4},
            )
        )
    with set_context(top_subckt.elements):
        top_subckt.elements.append(
            Instance(
                name="XTT1",
                model="TRUNK_CKT",
                pins={"TD": "D", "TG": "G", "TS": "S", "TB": "B"},
            )
        )
    return library


def test_remove_dummy_hier(dbr):
    assert dbr.find("TOP_CKT").name == "TOP_CKT"
    top = dbr.find("TOP_CKT")
    assert dbr.find("TRUNK_CKT").name == "TRUNK_CKT"
    trunk = dbr.find("TRUNK_CKT")
    assert dbr.find("LEAF_CKT").name == "LEAF_CKT"
    leaf = dbr.find("LEAF_CKT")
    assert leaf.elements[0].name == "M1"
    assert leaf.elements[0].model == "TESTMOS"
    dummy_hiers = []
    find_dummy_hier(dbr, top, dummy_hiers)
    assert "LEAF_CKT" in dummy_hiers
    assert "TRUNK_CKT" in dummy_hiers
    remove_dummies(dbr, ["LEAF_CKT"], "TOP_CKT")
    assert trunk.elements[0].name == "XTR1"
    assert trunk.elements[0].model == "TESTMOS"
    assert trunk.elements[0].parameters == {
        "PARAM1": "1.0",
        "M": "1",
        "PARAM2": "2",
        "PARAM": "4",
    }
    assert trunk.elements[0].pins == {"D": "TD", "G": "TG", "S": "TS", "B": "TB"}
    remove_dummies(dbr, ["TRUNK_CKT"], "TOP_CKT")
    assert top.elements[0].name == "XTT1"
    assert top.elements[0].model == "TESTMOS"
    assert top.elements[0].parameters == {
        "PARAM1": "1.0",
        "M": "1",
        "PARAM2": "2",
        "PARAM": "1",
    }
    assert top.elements[0].pins == {"D": "D", "G": "G", "S": "S", "B": "B"}


@pytest.fixture
def dbswap():
    library = Library()
    with set_context(library):
        model_pmos = Model(name="PMOS", pins=["D", "G", "S", "B"])
        library.append(model_pmos)
        model_nmos = Model(name="NMOS", pins=["D", "G", "S", "B"])
        library.append(model_nmos)
        subckt = SubCircuit(
            name="SUBCKT", pins=["VDD", "G", "GND", "B"], parameters=None
        )
        library.append(subckt)
    with set_context(subckt.constraints):
        subckt.constraints.append(constraint.GroundPorts(ports=["GND"]))
        subckt.constraints.append(constraint.PowerPorts(ports=["VDD"]))

    with set_context(subckt.elements):
        subckt.elements.append(
            Instance(
                name="M1",
                model="PMOS",
                pins={"D": "VDD", "G": "G", "S": "GND", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M2",
                model="PMOS",
                pins={"D": "NET1", "G": "G", "S": "VDD", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M3",
                model="PMOS",
                pins={"D": "NET1", "G": "G", "S": "GND", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M4",
                model="NMOS",
                pins={"D": "VDD", "G": "G", "S": "GND", "B": "B"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M5",
                model="NMOS",
                pins={"D": "GND", "G": "G", "S": "VDD", "B": "B"},
            )
        )
    return subckt


def test_swap(dbswap):
    assert dbswap.get_element("M1").name == "M1"
    assert dbswap.get_element("M1").pins == {"D": "VDD", "G": "G", "S": "GND", "B": "B"}
    define_SD(dbswap)
    assert dbswap.get_element("M1").pins == {"D": "GND", "G": "G", "S": "VDD", "B": "B"}
    assert dbswap.get_element("M2").pins == {"D": "NET1", "G": "G", "S": "VDD", "B": "B"}
    assert dbswap.get_element("M3").pins == {"D": "GND", "G": "G", "S": "NET1", "B": "B"}
    assert dbswap.get_element("M4").pins == {"D": "VDD", "G": "G", "S": "GND", "B": "B"}
    assert dbswap.get_element("M5").pins == {"D": "VDD", "G": "G", "S": "GND", "B": "B"}


@pytest.fixture
def dbdcap():
    library = Library()
    with set_context(library):
        model_pmos = Model(name="PMOS", pins=["D", "G", "S", "B"])
        library.append(model_pmos)
        model_nmos = Model(name="NMOS", pins=["D", "G", "S", "B"])
        library.append(model_nmos)
        subckt = SubCircuit(name="SUBCKT", pins=["VDD", "G", "OUT", "VSS"], parameters=None)
        library.append(subckt)

    with set_context(subckt.constraints):
        subckt.constraints.append(constraint.GroundPorts(ports=["VSS"]))
        subckt.constraints.append(constraint.PowerPorts(ports=["VDD"]))

    with set_context(subckt.elements):
        subckt.elements.append(
            Instance(
                name="M1",
                model="PMOS",
                pins={"D": "OUT", "G": "G", "S": "VDD", "B": "VDD"},
            )
        )
        subckt.elements.append(
            Instance(
                name="M2",
                model="NMOS",
                pins={"D": "OUT", "G": "G", "S": "VSS", "B": "VSS"},
            )
        )
        subckt.elements.append(  # poly
            Instance(
                name="M3",
                model="NMOS",
                pins={"D": "OUT", "G": "VSS", "S": "G", "B": "VSS"},
            )
        )
        subckt.elements.append(  # half
            Instance(
                name="M4",
                model="NMOS",
                pins={"D": "OUT", "G": "VSS", "S": "VSS", "B": "VSS"},
            )
        )
        subckt.elements.append(  # full
            Instance(
                name="M5",
                model="NMOS",
                pins={"D": "OUT", "G": "OUT", "S": "OUT", "B": "VSS"},
            )
        )
        subckt.elements.append(  # signal
            Instance(
                name="M6",
                model="NMOS",
                pins={"D": "OUT", "G": "OUT", "S": "OUT", "B": "VSS"},
            )
        )
    return subckt


def test_remove_dummy_devices(dbdcap):
    assert [e.name for e in dbdcap.elements] == ["M1", "M2", "M3", "M4", "M5", "M6"]
    remove_dummy_devices(dbdcap)
    assert [e.name for e in dbdcap.elements] == ["M1", "M2"]
