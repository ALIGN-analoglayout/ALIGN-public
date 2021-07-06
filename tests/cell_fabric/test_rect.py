from align.cell_fabric.transformation import Rect

def test_canonical():
    r = Rect( 0, 0, 1, 1)
    assert r.canonical().toList() == [0, 0, 1, 1]
    r = Rect( 1, 1, 0, 0)
    assert r.canonical().toList() == [0, 0, 1, 1]

def test_representations():
    r = Rect( 0, 0, 1, 1)    
    assert r.__repr__() == "[0, 0, 1, 1]"
    assert repr(r) == "[0, 0, 1, 1]"
    assert r.toColonSepStr() == "0:0:1:1"
    assert r.toList() == [0, 0, 1, 1]
