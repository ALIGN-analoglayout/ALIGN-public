import z3
import pytest
from align.circuit import constraint

@pytest.fixture
def solver():
    return z3.Solver()

def test_AlignHorizontal_input_sanitation(solver):
    x = constraint.AlignHorizontal(blocks=['M1', 'M2'], alignment='top')
    x = constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'], alignment='top')
    with pytest.raises(Exception):
        x = constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'], alignment='garbage')

def test_AlignHorizontal_nblock_checking(solver):
    x = constraint.AlignHorizontal(blocks=[], alignment='top')
    with pytest.raises(AssertionError):
        x.check()
    x = constraint.AlignHorizontal(blocks=['M1'], alignment='top')
    with pytest.raises(AssertionError):
        x.check()

def test_AlignHorizontal_order_checking(solver):
    x = constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'])
    x.check(solver)
    x = constraint.AlignHorizontal(blocks=['M4', 'M5'], alignment='bottom')
    x.check(solver)
    x = constraint.AlignHorizontal(blocks=['M3', 'M2'], alignment='bottom')
    with pytest.raises(AssertionError):
        x.check(solver)

def test_ConstraintDB_inputapi():
    db = constraint.ConstraintDB()
    with pytest.raises(Exception):
        db.append('garbage')

def test_ConstraintDB_checking():
    db = constraint.ConstraintDB()
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3']))
    db.append(constraint.AlignHorizontal(blocks=['M4', 'M5'], alignment='bottom'))
    with pytest.raises(AssertionError):
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], alignment='bottom'))