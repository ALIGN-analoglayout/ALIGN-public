
from cell_fabric.remove_duplicates import RemoveDuplicates

def test_touching():
    rA = [0,0,1,1]
    rB = [1,1,2,2]
    assert RemoveDuplicates.touching(rA,rB)

    rA = [0,0,1,1]
    rB = [2,2,3,3]
    assert not RemoveDuplicates.touching(rA,rB)

    rA = [0,0,100,100]
    rB = [50,50,51,51]
    assert RemoveDuplicates.touching(rA,rB)

    rA = [0,0,100,100]
    rB = [99,50,101,51]
    assert RemoveDuplicates.touching(rA,rB)

    rA = [0,0,100,100]
    rB = [101,50,102,51]
    assert not RemoveDuplicates.touching(rA,rB)
