import pytest
from cell_fabric import Canvas, Wire

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
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [200, -50, 600, 50]}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 1
    assert newTerminals[0]['rect'] == [0, -50, 600, 50]

import re

def test_short(capfd):
    (out, err) = capfd.readouterr()
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'y', 'rect': [200, -50, 600, 50]}]
    c.removeDuplicates()
    
#    p = re.compile( 'SHORT')
#    assert p.match(out) is not None, out


def test_underlapping():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [100, -50, 200, 50]}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 1
    assert newTerminals[0]['rect'] == [0, -50, 300, 50]

def test_disjoint():
    c = Canvas()
    c.addGen( Wire( nm='m2', layer='metal2', direction='h', clg=None, spg=None))
    c.terminals = [{'layer': 'metal2', 'netName': 'x', 'rect': [0, -50, 300, 50]},
                   {'layer': 'metal2', 'netName': 'x', 'rect': [400, -50, 600, 50]}]
    newTerminals = c.removeDuplicates()
    assert len(newTerminals) == 2
    assert newTerminals[0]['rect'] == [0, -50, 300, 50]
    assert newTerminals[1]['rect'] == [400, -50, 600, 50]
