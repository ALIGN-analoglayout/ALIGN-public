from align.cell_fabric import Canvas, Wire, Via

def test_vertical():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='metal1', direction='v', clg=None, spg=None))
    c.terminals = [{'layer': 'metal1', 'netName': 'x', 'rect': [0, 0, 100, 300], 'netType': 'drawing'}]
    c.removeDuplicates()

def test_horizontal():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, 0, 300, 100], 'netType': 'drawing'}]
    c.removeDuplicates() 

def test_different_widths():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [0, -60, 300, 60], 'netType': 'drawing'}]
    c.removeDuplicates()
    assert len(c.rd.different_widths) > 0

def test_overlapping():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [200, -50, 600, 50], 'netType': 'drawing'}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 1
    assert newTerminals[0]['rect'] == [0, -50, 600, 50]

def test_short():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'y', 'rect': [200, -50, 600, 50], 'netType': 'drawing'}]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 1, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens

def test_open():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [400, -50, 600, 50], 'netType': 'drawing'}]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 1, c.rd.opens

def test_metal_terminal_connection():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'M1:S', 'rect': [200, -50, 600, 50], 'netType': 'drawing'}]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert len(c.rd.subinsts) == 1, c.rd.subinsts

def test_metal_multi_terminal_open():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'M1:S', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'M1:D', 'rect': [200, -50, 600, 50], 'netType': 'drawing'}]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 2, c.rd.opens
    assert len(c.rd.subinsts) == 1, c.rd.subinsts
    assert len(c.rd.subinsts['M1'].pins) == 2, c.rd.subinsts

def test_metal_multi_terminal_connection():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'M1:S', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'inp1', 'rect': [200, -50, 600, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'M1:D', 'rect': [400, -50, 800, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': None, 'rect': [700, -50, 1000, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'M2:inp', 'rect': [900, -50, 1200, 50], 'netType': 'drawing'}]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert len(c.rd.subinsts) == 2
    assert len(c.rd.subinsts['M1'].pins) == 2, c.rd.subinsts
    assert len(c.rd.subinsts['M2'].pins) == 1

def test_via_connecta():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': 'b', 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectb():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'b', 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': None, 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': 'b', 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectc():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'b', 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectd():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connecte():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': None, 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': 'b', 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_connectf():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'b', 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': None, 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    terms = c.removeDuplicates()
    print(terms)
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert { d['netName'] for d in terms} == { 'b'}

def test_via_short1():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'a', 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'b', 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    print(c.removeDuplicates())
    assert len(c.rd.shorts) == 1, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens

def test_underlapping():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [100, -50, 200, 50], 'netType': 'drawing'}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 1
    assert newTerminals[0]['rect'] == [0, -50, 300, 50]

def test_disjoint():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [  0, -50, 300, 50], 'netType': 'drawing'},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [400, -50, 600, 50], 'netType': 'drawing'}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 2
    assert newTerminals[0]['rect'] == [  0, -50, 300, 50]
    assert newTerminals[1]['rect'] == [400, -50, 600, 50]

def test_via_terminal_connection():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'a', 'rect':   [  0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'M1:S', 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'}
    ]
    print(c.removeDuplicates())
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert len(c.rd.subinsts) == 1, c.rd.subinsts
    assert len(c.rd.subinsts['M1'].pins) == 1

def test_via_multi_terminal_connection():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'x', 'rect':  [ 0, -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'M1:S', 'rect': [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'M1:D', 'rect': [0, -150, 50, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [0,  -50, 50,  50], 'netType': 'drawing'}
    ]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert len(c.rd.subinsts) == 1, c.rd.subinsts
    assert len(c.rd.subinsts['M1'].pins) == 2, c.rd.subinsts

def test_via_multi_terminal_open():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.addGen( Via( nm="v1", layer="via1", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M2', 'netName': None, 'rect': [0,  -50, 300,  50], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'M1:S', 'rect': [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'M1:D', 'rect': [0, -150, 50, 150], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [100,  -50, 200,  50], 'netType': 'drawing'},
                   {'layer': 'via1', 'netName': None, 'rect': [0,  -50, 50,  50], 'netType': 'drawing'}
    ]
    c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 2, c.rd.opens
    assert len(c.rd.subinsts) == 1, c.rd.subinsts
    assert len(c.rd.subinsts['M1'].pins) == 2, c.rd.subinsts

def test_via_multi_terminal_short():
    c = Canvas()
    c.addGen( Wire( nm='m1', layer='M1', direction='v', clg=None, spg=None))
    c.addGen( Via( nm="v0", layer="via0", h_clg=None, v_clg=None))
    c.terminals = [{'layer': 'M1', 'netName': 'x', 'rect':   [100, -150, 200, 150], 'netType': 'drawing'},
                   {'layer': 'M1', 'netName': 'y', 'rect':   [300, -150, 600, 150], 'netType': 'drawing'},
                   {'layer': 'via0', 'netName': 'M1:S', 'rect': [100,  -50, 200,  50], 'netType': 'drawing'},
                   {'layer': 'via0', 'netName': 'M1:S', 'rect': [300,  -50, 600,  50], 'netType': 'drawing'}
    ]
    c.layer_stack.append( ('via0', ('M1', None)))
    c.removeDuplicates()
    assert len(c.rd.subinsts) == 1, c.rd.subinsts
    assert len(c.rd.subinsts['M1'].pins) == 1, c.rd.subinsts
    assert len(c.rd.shorts) == 1, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens

def test_blockage_not_merging():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'M2', 'netName': 'a', 'rect': [ 0, -50, 300, 50], 'netType': 'pin'},
                   {'layer': 'M2', 'netName': None, 'rect': [ 150, -50, 750, 50], 'netType': 'blockage'}
    ]
    newTerminals = c.removeDuplicates()
    assert len(c.rd.shorts) == 0, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
    assert len(newTerminals) == 2, len(newTerminals)

def test_overlapping_drawings_through_blockage():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='M2', direction='h', clg=None, spg=None))
    c.terminals = [ {'layer': 'M2', 'netName': 'a', 'rect': [ 0, -50, 300, 50], 'netType': 'pin'},
                    {'layer': 'M2', 'netName': None, 'rect': [ 150, -50, 750, 50], 'netType': 'blockage'},
                    {'layer': 'M2', 'netName': 'b', 'rect': [ 600, -50, 900, 50], 'netType': 'pin'}
    ]
    newTerminals = c.removeDuplicates()
    assert len(c.rd.shorts) == 1, c.rd.shorts
    assert len(c.rd.opens) == 0, c.rd.opens
