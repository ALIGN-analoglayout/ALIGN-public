import pytest

import circuit

def test_combined():
    ckt = circuit.Circuit()
    mysubckt = circuit.SubCircuit('mysubckt', 'pin1', 'pin2', param1=1, param2=1e-3, param3="0.1f", param4="hello")
    X1 = ckt.add_element(mysubckt('X1', 'net10', 'net12'))
    X1.add_element(circuit.library['NMOS']('M1', 'pin1', 'net10', 'net13', 'vss'))
    X1.add_element(circuit.library['NMOS']('M2', 'pin2', 'net10', 'net13', 'vss'))
    _ = circuit.SubCircuit('mysubckt2', 'pin1', 'pin2', 'pin3')
    X2 = ckt.add_element(circuit.library['mysubckt2']('X2', 'net10', 'net12', 'net14'))
    X2.add_element(circuit.library['NMOS']('M1', 'pin1', 'pin3', 'net13', 'vss'))
    X2.add_element(circuit.library['NMOS']('M2', 'pin2', 'pin3', 'net13', 'vss'))
