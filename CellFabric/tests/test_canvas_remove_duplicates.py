import pytest
from cell_fabric import Canvas, Wire, Via

def test_vertical():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='metal1', direction='v', clg=None, spg=None))
    c.terminals = [{'layer': 'metal1', 'netName': 'x', 'rect': [0, 0, 100, 300]}]
    c.removeDuplicates()

def test_horizontal():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, 0, 300, 100]}]
    c.removeDuplicates() 

def test_different_widths():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [0, -60, 300, 60]}]
    with pytest.raises(AssertionError) as excinfo:
        c.removeDuplicates()
    assert "Rectangles on layer metal2 with the same centerline 0 but" in str(excinfo.value)

def test_overlapping():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [200, -50, 600, 50]}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 1
    assert newTerminals[0]['rect'] == [0, -50, 600, 50]

def test_short():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'y', 'rect': [200, -50, 600, 50]}]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 1

def test_open():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [400, -50, 600, 50]}]
    c.removeDuplicates()
    assert len(c.rd.opens) == 1

def test_via_connecta():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': 'b', 'rect': [100,  -50, 200,  50]}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectb():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'b', 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': None, 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': 'b', 'rect': [100,  -50, 200,  50]}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectc():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'b', 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50]}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectd():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50]}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connecte():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': None, 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': 'b', 'rect': [100,  -50, 200,  50]}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectf():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'b', 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': None, 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50]}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_short1():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'a', 'rect':   [  0,  -50, 300,  50]},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150]},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50]}
    ]
    print(c.removeDuplicates())
    assert len(c.rd.shorts) == 1

def test_underlapping():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [100, -50, 200, 50]}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 1
    assert newTerminals[0]['rect'] == [0, -50, 300, 50]

def test_disjoint():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [400, -50, 600, 50]}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 2
    assert newTerminals[0]['rect'] == [  0, -50, 300, 50]
    assert newTerminals[1]['rect'] == [400, -50, 600, 50]
