import z3
import pytest
from align.circuit import constraint

@pytest.fixture
def solver():
    return z3.Solver()

@pytest.fixture
def db():
    return constraint.ConstraintDB()

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

def test_ConstraintDB_inputapi(db):
    with pytest.raises(Exception):
        db.append('garbage')

def test_ConstraintDB_checking(db):
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3']))
    db.append(constraint.AlignHorizontal(blocks=['M4', 'M5'], alignment='bottom'))
    with pytest.raises(AssertionError):
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], alignment='bottom'))

def test_ConstraintDB_incremental_checking(db):
    '''
    ConstraintDB can be used to run experiments
    using checkpoint() and revert() methods. There
    is an overhead so use sparingly
    '''
    # Experiment 1 : Success
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3']))
    db.checkpoint()
    # Experiment 2 : Failure
    with pytest.raises(AssertionError):
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], alignment='bottom'))
    db.revert()
    # Experiment 3 : Success
    db.append(constraint.AlignHorizontal(blocks=['M4', 'M5'], alignment='bottom'))
    db.checkpoint()
    # Experiment 4: Failure
    with pytest.raises(AssertionError):
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], alignment='bottom'))
    db.revert()
    # Experiment 5: Success
    db.append(constraint.AlignHorizontal(blocks=['M2', 'M5']))
    # Experiments Completed ! Final Constraints:
    # constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'])
    # constraint.AlignHorizontal(blocks=['M4', 'M5'], alignment='bottom')
    # constraint.AlignHorizontal(blocks=['M2', 'M5'])

def test_ConstraintDB_nonincremental_revert(db):
    '''
    It is possible to revert() back to a certain
    checkpoint() by name. Needing to unroll multiple
    checkpoints can indicate suboptimal compiler design
    '''
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2']))
    idx = db.checkpoint()
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M3']))
    db.checkpoint()
    db.append(constraint.AlignHorizontal(blocks=['M2', 'M3']))
    db.checkpoint()
    db.revert(idx)
    assert len(db.constraints) == 1
    assert len(db._commits) == 0
    assert 'M3' not in str(db._solver)