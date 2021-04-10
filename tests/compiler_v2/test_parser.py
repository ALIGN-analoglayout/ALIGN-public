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

    assert circuit.elements[0].name == 'MM0' # can we directly use instance name instead of index?
    assert circuit.elements[0].model.name == 'NMOS_RVT'
    assert circuit.elements[0].model.base.name == 'NMOS'
    assert circuit.elements[0].model.base.pins == ['D','G','S','B']
    assert circuit.elements[0].model.pins == ['D','G','S','B']
    assert circuit.elements[0].model.base.parameters == {'W': '0', 'L': '0', 'NFIN': '1'}  # TBF: NF is missing, W==0? 
    #TBF: Document base model 
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
    assert circuit.elements[3].model.base == None # Using base model
    assert circuit.elements[3].model.pins == ['+','-']
    assert circuit.elements[3].model.parameters == {'VALUE':'0'}
    assert circuit.elements[3].model.prefix == 'R'
    assert circuit.elements[3].pins == {'+': 'VBIAS', '-': 'NET5'}
    assert circuit.elements[3].parameters == {'VALUE': '5000'}
    
    assert circuit.elements[4].name == 'CC0'
    assert circuit.elements[4].model.name == 'CAP'
    assert circuit.elements[4].model.base == None
    assert circuit.elements[4].pins == {'+': 'VIN', '-': 'NET5'}
    assert circuit.elements[4].parameters == {'VALUE': '1.0000000000000002E-14'} # TBF: remove multiple zeros
    
    assert circuit.elements[5].name == 'LL0'
    assert circuit.elements[5].model.name == 'IND'
    assert circuit.elements[5].model.base == None 
    assert circuit.elements[5].pins == {'+': 'VDD!', '-': 'VOUT'}
    assert circuit.elements[5].parameters == {'VALUE': '0.002'} #TBF: change to scientific nomenclature?
    
    assert circuit.elements[6].name == 'RR1'
    assert circuit.elements[6].model.name == 'RESISTOR'
    assert circuit.elements[6].model.base.name == 'RES'
    assert circuit.elements[6].model.pins == ['+', '-']
    assert circuit.elements[6].model.parameters == {'RES':'1','VALUE':'0'}
    assert circuit.elements[6].pins == {'+': 'VBIAS', '-': 'NET6'}
    assert circuit.elements[6].parameters == {'RES':'5000','VALUE': '0'}

    assert circuit.elements[7].name == 'CC1'
    assert circuit.elements[7].model.name == 'CAPACITOR'
    assert circuit.elements[7].model.base.name == 'CAP'
    assert circuit.elements[7].model.pins == ['+', '-']
    assert circuit.elements[7].model.parameters == {'CAP':'1','VALUE':'0'}
    assert circuit.elements[7].pins == {'+': 'VIN', '-': 'NET6'}
    assert circuit.elements[7].parameters == {'CAP': '1.0000000000000002E-14', 'VALUE': '0'}
    
    assert circuit.elements[8].name == 'LL1'
    assert circuit.elements[8].model.name == 'INDUCTOR'
    assert circuit.elements[8].model.base.name == 'IND'
    assert circuit.elements[8].model.pins == ['+', '-']
    assert circuit.elements[8].model.parameters == {'IND':'1','VALUE':'0'}
    assert circuit.elements[8].pins == {'+': 'VDD!', '-': 'NET6'}
    assert circuit.elements[8].parameters == {'IND': '0.002', 'VALUE': '0'}
    
def test_top_level():
    test_path = (pathlib.Path(__file__).parent / 'test_circuits' / 'test1.sp').resolve()
    pdk_dir = pathlib.Path(__file__).resolve().parent.parent.parent / 'pdks' / 'FinFET14nm_Mock_PDK'
    config_path =  pathlib.Path(__file__).resolve().parent.parent.parent / 'align' / 'config' 
    circuit = compiler(test_path, "test1", pdk_dir, config_path) # Not able to parse spice files with no top level names
    assert len(circuit.elements) == 9
