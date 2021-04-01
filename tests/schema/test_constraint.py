import pytest
from align.schema import constraint

try:
    import z3
except:
    z3 = None

@pytest.fixture
def solver():
    return z3.Solver()

@pytest.fixture
def db():
    return constraint.ConstraintDB()

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_AlignHorizontal_input_sanitation(solver):
    x = constraint.AlignHorizontal(blocks=['M1', 'M2'], line='top')
    x = constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'], line='top')
    with pytest.raises(Exception):
        x = constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'], line='garbage')

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_AlignHorizontal_nblock_checking(solver):
    x = constraint.AlignHorizontal(blocks=[], line='top')
    with pytest.raises(AssertionError):
        x.check()
    x = constraint.AlignHorizontal(blocks=['M1'], line='top')
    with pytest.raises(AssertionError):
        x.check()

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_AlignHorizontal_order_checking(solver):
    '''
    This is just a unittest of generated constraints

    Please use ConstraintDB to manage constraints
    (See test_ConstraintDB_checking() for example)
    '''
    x = constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'])
    solver.append(*x.check())
    assert solver.check() == z3.sat
    x = constraint.AlignHorizontal(blocks=['M4', 'M5'], line='bottom')
    solver.append(*x.check())
    assert solver.check() == z3.sat
    x = constraint.AlignHorizontal(blocks=['M3', 'M2'], line='bottom')
    solver.append(*x.check())
    with pytest.raises(AssertionError):
        assert solver.check() == z3.sat

def test_ConstraintDB_inputapi(db):
    with pytest.raises(Exception):
        db.append('garbage')

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_ConstraintDB_checking(db):
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3']))
    db.append(constraint.AlignHorizontal(blocks=['M4', 'M5'], line='bottom'))
    with pytest.raises(AssertionError):
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], line='bottom'))

@pytest.mark.skipif(z3 is None, reason="requires z3")
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
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], line='bottom'))
    db.revert()
    # Experiment 3 : Success
    db.append(constraint.AlignHorizontal(blocks=['M4', 'M5'], line='bottom'))
    db.checkpoint()
    # Experiment 4: Failure
    with pytest.raises(AssertionError):
        db.append(constraint.AlignHorizontal(blocks=['M3', 'M2'], line='bottom'))
    db.revert()
    # Experiment 5: Success
    db.append(constraint.AlignHorizontal(blocks=['M2', 'M5']))
    # Experiments Completed ! Final Constraints:
    # constraint.AlignHorizontal(blocks=['M1', 'M2', 'M3'])
    # constraint.AlignHorizontal(blocks=['M4', 'M5'], line='bottom')
    # constraint.AlignHorizontal(blocks=['M2', 'M5'])

def test_ConstraintDB_nonincremental_revert(db):
    '''
    While it is possible to revert() back to a certain
    checkpoint() by name, needing to unroll multiple
    checkpoints can indicate suboptimal compiler design
    '''
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2']))
    idx = db.checkpoint()
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M3']))
    db.checkpoint()
    db.append(constraint.AlignHorizontal(blocks=['M2', 'M3']))
    db.checkpoint()
    db.revert(idx)
    assert len(db) == 1
    assert len(db._commits) == 0
    if db._validation:
        assert 'M3' not in str(db._solver)

def test_ConstraintDB_permissive():
    '''
    Check that it is possible to turn validation OFF
    NOT RECOMMENDED !! DO NOT DO THIS !!!
    '''
    db = constraint.ConstraintDB(validation=False)
    db.append(constraint.AlignHorizontal(blocks=['M1', 'M2']))
    db.append(constraint.AlignHorizontal(blocks=['M2', 'M1']))
