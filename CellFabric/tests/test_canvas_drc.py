from cell_fabric import Canvas, Pdk, Wire

def test_min_length_pass():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')

    c = Canvas(p)
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    # L(300) > MinL(180)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]}]
    c.gen_data()
    assert c.drc.num_errors == 0

    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    # L(300) > MinL(200)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [0, 0, 300, 100]}]
    c.gen_data()
    assert c.drc.num_errors == 0

def test_min_length_fail():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')

    c = Canvas(p)
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    # L(175) < MinL(180)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 175]}]
    c.gen_data()
    assert c.drc.num_errors == 1

    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    # L(190) < MinL(200)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [0, 0, 190, 100]}]
    c.gen_data()
    assert c.drc.num_errors == 1

def test_min_spacing_pass():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')

    c = Canvas(p)
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    # space(50) > End-To-End(48)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]},
                   {'layer': 'M1', 'netName': 'x', 'rect': [0, 350, 100, 650]}]
    c.gen_data()
    assert c.drc.num_errors == 0

    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    # space(50) > End-To-End(48)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [  0, -50, 200, 50]},
                   {'layer': 'M2', 'netName': 'x', 'rect': [250, -50, 600, 50]}]
    c.gen_data()
    assert c.drc.num_errors == 0

def test_min_spacing_fail():
    p = Pdk().load('../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')

    c = Canvas(p)
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    # space(40) < End-To-End(48)
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect': [0, 0, 100, 300]},
                   {'layer': 'M1', 'netName': 'x', 'rect': [0, 340, 100, 640]}]
    c.gen_data()
    assert c.drc.num_errors == 1

    c = Canvas(p)
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    # space(40) < End-To-End(48)
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect': [  0, -50, 200, 50]},
                   {'layer': 'M2', 'netName': 'x', 'rect': [240, -50, 600, 50]}] #End-To-End is 48
    c.gen_data()
    assert c.drc.num_errors == 1
