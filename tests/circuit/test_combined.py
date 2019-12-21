import circuit
# from pathlib import Path
# import sys

def test_combined():
    library = circuit.Library()
    ckt = circuit.Circuit()
    # Not registering subckt to library (though I really should)
    mysubckt = circuit.SubCircuit('mysubckt', 'pin1', 'pin2', param1=1, param2=1e-3, param3="0.1f", param4="hello")
    mysubckt.add_element(library['NMOS']('M1', 'pin1', 'net10', 'net13', 'vss'))
    mysubckt.add_element(library['NMOS']('M2', 'pin2', 'net10', 'net13', 'vss'))
    X1 = ckt.add_element(mysubckt('X1', 'net10', 'net12'))
    # Registering & reusing subckt from library (correct behavior)
    _ = circuit.SubCircuit('mysubckt2', 'pin1', 'pin2', 'pin3', library=library)
    library['mysubckt2'].add_element(library['NMOS']('M1', 'pin1', 'pin3', 'net13', 'vss'))
    library['mysubckt2'].add_element(library['NMOS']('M2', 'pin2', 'pin3', 'net13', 'vss'))
    X2 = ckt.add_element(library['mysubckt2']('X2', 'net10', 'net12', 'net14'))
    assert ckt.elements == [X1, X2]
    assert ckt.nets == ['net10', 'net12', 'net14']

def test_replace_matching_subckts():
    # parse subckts
    parser = circuit.SpiceParser()
    with open('tests/basic_template.sp') as fp:
        parser.parse(fp.read())
    primitivelib = circuit.Library({x: y for x, y in parser.library.items() if issubclass(y, circuit.core._SubCircuit)})
    # parse netlist
    parser = circuit.SpiceParser()
    with open('tests/ota.cir') as fp:
        parser.parse(fp.read())
    # Extract ckt
    ckt = parser.library['OTA'].circuit
    ckt.flatten()
    # Sort subckts using hypothetical complexity cost
    subckts = list(primitivelib.values())
    subckts.sort(key=lambda x: len(x.elements)*10000 - 100 * len(x._pins) + len(x.nets), reverse=True)
    assert len(ckt.elements) == 10
    assert all(x.name.startswith('M') for x in ckt.elements)
    # Perform subgraph matching & replacement
    ckt.replace_matching_subckts(subckts)
    assert len(ckt.elements) == 5
    assert all(x.name.startswith('X') for x in ckt.elements)
    # # Generate primitive layouts
    # sys.path.append( str(Path(__file__).parent.parent.parent / 'PDK_Abstraction' / 'FinFET14nm_Mock_PDK'))
    # import primitive
    # for element in ckt.elements:
    #     uc = primitive.PrimitiveGenerator(12, 4, 2, 3)
    #     with open(element.name + '.json', "wt") as fp:
    #         uc.writeJSON(fp)
    # Generate placer, router input

def test_replace_repeated_subckts():
    # parse netlist
    parser = circuit.SpiceParser()
    with open('tests/ota.cir') as fp:
        parser.parse(fp.read())
    # Extract ckt
    ckt = parser.library['OTA'].circuit
    ckt.flatten()
    subckts = ckt.replace_repeated_subckts()
    assert len(subckts) == 1
    assert len(subckts[0].elements) == 4
    elements = {x.name for x in subckts[0].elements}
    assert elements == {'M10', 'M7', 'M9', 'M1'} or elements == {'M2', 'M6', 'M8', 'M0'}
