import pytest
import pathlib
from align.schema import constraint
from align.schema.checker import Z3Checker, CheckerError

@pytest.fixture
def db():
    return constraint.ConstraintDB()

@pytest.fixture
def checker():
    return Z3Checker()

def test_Order_input_sanitation():
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
    with pytest.raises(Exception):
        x = constraint.Order(direction='lefta_to_rightb', instances=['M1', 'M2', 'M3'])

def test_Order_constraintname():
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])
    assert x.constraint == 'order'

def test_Order_nblock_checking():
    x = constraint.Order(direction='left_to_right', instances=[])
    with pytest.raises(AssertionError):
        x.check(None)
    x = constraint.Order(direction='left_to_right', instances=['M1'])
    with pytest.raises(AssertionError):
        x.check(None)

def test_ConstraintDB_inputapi(db):
    class Garbage(constraint.PlacementConstraint):
        test: str = 'hello'
        def check(self):
            pass
    with pytest.raises(Exception):
        db.append(Garbage())

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_Order_smt_checking(checker):
    x = constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
    x.check(checker)
    x = constraint.Order(direction='left_to_right', instances=['M4', 'M5'])
    x.check(checker)
    x = constraint.Order(direction='left_to_right', instances=['M3', 'M2'])
    with pytest.raises(CheckerError):
        x.check(checker)

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_Order_db_append(db):
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3']))
    db.append(constraint.Order(direction='left_to_right', instances=['M4', 'M5']))
    with pytest.raises(CheckerError):
        db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))

def test_AlignInOrder_input_sanitation():
    x = constraint.AlignInOrder(instances=['M1', 'M2'], line='top')
    x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], line='top')
    with pytest.raises(Exception):
        x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], line='garbage')

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_AlignInOrder_smt_checking(db):
    db.append(constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], direction='horizontal'))
    db.append(constraint.AlignInOrder(instances=['M4', 'M5'], line='bottom'))
    with pytest.raises(CheckerError):
        db.append(constraint.AlignInOrder(instances=['M3', 'M2'], line='bottom'))

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
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
    with pytest.raises(CheckerError):
        db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))
    db.revert()
    # Experiment 3 : Success
    db.append(constraint.Order(direction='left_to_right', instances=['M4', 'M5']))
    db.checkpoint()
    # Experiment 4: Failure
    with pytest.raises(CheckerError):
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
    if db._checker:
        assert 'M3' not in str(db._checker._solver)

def test_ConstraintDB_json(db):
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M3']))
    fp = pathlib.Path(__file__).parent / 'const.json'
    fp.write_text(db.json())
    newdb = constraint.ConstraintDB.parse_file(fp)
    assert db == newdb

def test_ConstraintDB_parent_relationship(db):
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
    db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M3']))
    for const in db:
        assert const.parent == db