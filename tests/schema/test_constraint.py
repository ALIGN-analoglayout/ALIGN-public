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

def test_Order_input_sanitation():
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
    with pytest.raises(Exception):
        x = constraint.Order(direction='lefta_to_rightb', instances=['M1', 'M2', 'M3'])

def test_Order_constraint():
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])
    assert x.constraint == 'order'

def test_Order_nblock_checking():
    x = constraint.Order(direction='left_to_right', instances=[])
    with pytest.raises(AssertionError):
        x.check()
    x = constraint.Order(direction='left_to_right', instances=['M1'])
    with pytest.raises(AssertionError):
        x.check()

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_Order_z3_checking(solver):
    '''
    This is just a unittest of generated constraints

    Please use ConstraintDB to manage constraints
    (See test_ConstraintDB_checking() for example)
    '''
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
    solver.append(*x.check())
    assert solver.check() == z3.sat
    x = constraint.Order(direction='left_to_right', instances=['M4', 'M5'])
    solver.append(*x.check())
    assert solver.check() == z3.sat
    x = constraint.Order(direction='left_to_right', instances=['M3', 'M2'])
    solver.append(*x.check())
    with pytest.raises(AssertionError):
        assert solver.check() == z3.sat

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_AlignInOrder_input_sanitation(solver):
    x = constraint.AlignInOrder(instances=['M1', 'M2'], line='top')
    x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], line='top')
    with pytest.raises(Exception):
        x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], line='garbage')

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_AlignInOrder_nblock_checking(solver):
    x = constraint.AlignInOrder(instances=[], line='top')
    with pytest.raises(AssertionError):
        x.check()
    x = constraint.AlignInOrder(instances=['M1'], line='top')
    with pytest.raises(AssertionError):
        x.check()

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_AlignInOrder_order_checking(solver):
    '''
    This is just a unittest of generated constraints

    Please use ConstraintDB to manage constraints
    (See test_ConstraintDB_checking() for example)
    '''
    x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], direction='horizontal')
    solver.append(*x.check())
    assert solver.check() == z3.sat
    x = constraint.AlignInOrder(instances=['M4', 'M5'], line='bottom')
    solver.append(*x.check())
    assert solver.check() == z3.sat
    x = constraint.AlignInOrder(instances=['M3', 'M2'], line='bottom')
    solver.append(*x.check())
    with pytest.raises(AssertionError):
        assert solver.check() == z3.sat

def test_ConstraintDB_inputapi(db):
    class Garbage(constraint.PlacementConstraint):
        test: str = 'hello'
        def check(self):
            pass
    with pytest.raises(Exception):
        db.append(Garbage())

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_ConstraintDB_checking(db):
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3']))
    db.append(constraint.Order(direction='left_to_right', instances=['M4', 'M5']))
    with pytest.raises(AssertionError):
        db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))

@pytest.mark.skipif(z3 is None, reason="requires z3")
def test_ConstraintDB_incremental_checking(db):
    '''
    ConstraintDB can be used to run experiments
    using checkpoint() and revert() methods. There
    is an overhead so use sparingly
    '''
    # Experiment 1 : Success
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3']))
    db.checkpoint()
    # Experiment 2 : Failure
    with pytest.raises(AssertionError):
        db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))
    db.revert()
    # Experiment 3 : Success
    db.append(constraint.Order(direction='left_to_right', instances=['M4', 'M5']))
    db.checkpoint()
    # Experiment 4: Failure
    with pytest.raises(AssertionError):
        db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))
    db.revert()
    # Experiment 5: Success
    db.append(constraint.Order(direction='left_to_right', instances=['M2', 'M5']))
    # Experiments Completed ! Final Constraints:
    # constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
    # constraint.Order(direction='left_to_right', instances=['M4', 'M5'])
    # constraint.Order(direction='left_to_right', instances=['M2', 'M5'])

def test_ConstraintDB_nonincremental_revert(db):
    '''
    While it is possible to revert() back to a certain
    checkpoint() by name, needing to unroll multiple
    checkpoints can indicate suboptimal compiler design
    '''
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
    idx = db.checkpoint()
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M3']))
    db.checkpoint()
    db.append(constraint.Order(direction='left_to_right', instances=['M2', 'M3']))
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
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
    db.append(constraint.Order(direction='left_to_right', instances=['M2', 'M1']))
