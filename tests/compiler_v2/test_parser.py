import pathlib

from align.compiler_v2.main import compiler


def test_simple_circuit():
    test_path = (pathlib.Path(__file__).parent / 'test_circuits' / 'test2.sp').resolve()
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    config_path =  pathlib.Path(__file__).resolve().parent.parent.parent / 'align' / 'config' 
    circuit = compiler(test_path, "test2", pdk_dir, config_path)
    assert len(circuit.elements) == 9
    assert len(circuit.nets) == 10
    assert circuit.name == "TEST2"
    assert len(circuit.pins) == 3

    assert circuit.elements[0].name == 'MM0' # can we directly use instance name?
    assert circuit.elements[0].model.name == 'NMOS_RVT'
    assert circuit.elements[0].model.base.name == 'NMOS'
    assert circuit.elements[0].model.base.pins == ['D','G','S','B']
    assert circuit.elements[0].model.base.parameters == {'W':'0', 'L':'0', 'NFIN':'1'} # NF is missing, W==0?
    assert circuit.elements[0].model.base.prefix == 'M'
    assert circuit.elements[0].pins == {'D': 'VOUT', 'G': 'NET5', 'S': 'GND!', 'B': 'GND!'}
    assert circuit.elements[0].parameters == {'W':'2.7E-08', 'L':'2E-08', 'NFIN':'1', 'NF':'1'}

    assert circuit.elements[1].name == 'MM2'
    assert circuit.elements[1].model.name == 'N'
    assert circuit.elements[1].pins == {'D': 'VOUT', 'G': 'NET2', 'S': 'NET3', 'B': 'GND!'}
    assert circuit.elements[1].parameters == {'W': '2.7E-08', 'L': '2E-08', 'NFIN': '1', 'NF': '1', 'M': '1'}

    assert circuit.elements[2].name == 'MM3'
    assert circuit.elements[2].model.name == 'NFET'
    assert circuit.elements[2].pins == {'D': 'VOUT', 'G': 'NET3', 'S': 'NET4', 'B': 'GND!'}
    assert circuit.elements[2].parameters == {'W': '2.7E-08', 'L': '2E-08', 'NFIN': '1', 'NF': '1', 'M': '1'}
    
    assert circuit.elements[3].name == 'RR0'
    assert circuit.elements[3].model.name == 'RES'
    assert circuit.elements[3].model.base == None #why is this none?
    # assert circuit.elements[3].model.base.pins == ['+','-']
    # assert circuit.elements[3].model.base.parameters == {'R':'1'}
    # assert circuit.elements[3].model.base.prefix == 'R'
    assert circuit.elements[3].pins == {'+': 'VBIAS', '-': 'NET5'}
    assert circuit.elements[3].parameters == {'VALUE': '5000'}
    
    assert circuit.elements[4].name == 'CC0'
    assert circuit.elements[4].model.name == 'CAP'
    assert circuit.elements[4].model.base == None #why is this none?
    assert circuit.elements[4].pins == {'+': 'VIN', '-': 'NET5'}
    assert circuit.elements[4].parameters == {'VALUE': '1.0000000000000002E-14'} #To be fixed
    
    assert circuit.elements[5].name == 'LL0'
    assert circuit.elements[5].model.name == 'IND'
    assert circuit.elements[5].model.base == None #why is this none?
    assert circuit.elements[5].pins == {'+': 'VDD!', '-': 'VOUT'}
    assert circuit.elements[5].parameters == {'VALUE': '2E-3'}
    
    assert circuit.elements[6].name == 'RR1'
    assert circuit.elements[6].model.name == 'RES'
    assert circuit.elements[6].model.base == None #why is this none?
    assert circuit.elements[6].pins == {'+': 'VBIAS', '-': 'NET5'}
    assert circuit.elements[6].parameters == {'VALUE': '5000'}