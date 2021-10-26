import pytest
import pathlib
from align.schema import constraint, Model, Instance, SubCircuit, Library
from align.schema.checker import Z3Checker, CheckerError
from align.schema.types import set_context

@pytest.fixture
def db():
    library = Library()
    with set_context(library):
        model = Model(
            name='TwoTerminalDevice',
            pins=['A', 'B'],
            parameters={'MYPARAMETER': '3'})
        library.append(model)
        subckt = SubCircuit(
            name = 'SUBCKT',
            pins = ['PIN1', 'PIN2'],
            parameters = {'PARAM1':1, 'PARAM2':'1E-3'})
        library.append(subckt)
    with set_context(subckt.elements):
        subckt.elements.append(Instance(name='M1', model='TwoTerminalDevice', pins={'A': 'NET1', 'B': 'NET2'},generator='Dummy'))
        subckt.elements.append(Instance(name='M2', model='TwoTerminalDevice', pins={'A': 'NET2', 'B': 'NET3'},generator='Dummy'))
        subckt.elements.append(Instance(name='M3', model='TwoTerminalDevice', pins={'A': 'NET1', 'B': 'NET2'},generator='Dummy'))
        subckt.elements.append(Instance(name='M4', model='TwoTerminalDevice', pins={'A': 'NET2', 'B': 'NET3'},generator='Dummy'))
        subckt.elements.append(Instance(name='M5', model='TwoTerminalDevice', pins={'A': 'NET1', 'B': 'NET2'},generator='Dummy'))
        subckt.elements.append(Instance(name='M6', model='TwoTerminalDevice', pins={'A': 'NET2', 'B': 'NET3'},generator='Dummy'))
    return subckt.constraints

@pytest.fixture
def checker():
    return Z3Checker()

def test_Order_input_sanitation(db):
    with set_context(db):
        x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])
        x = constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
        with pytest.raises(Exception):
            x = constraint.Order(direction='lefta_to_rightb', instances=['M1', 'M2', 'M3'])

def test_Order_constraintname(db):
    with set_context(db):
        x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])
    assert x.constraint == 'order'

def test_Order_nblock_checking(db):
    with set_context(db):
        x = constraint.Order(direction='left_to_right', instances=[])
    with pytest.raises(AssertionError):
        x.check(None)
    with set_context(db):
        x = constraint.Order(direction='left_to_right', instances=['M1'])
    with pytest.raises(AssertionError):
        x.check(None)

@pytest.mark.skip(reason='Cannot activate this yet because of ALIGN1.0 annotation issues')
def test_Order_validate_instances(db):
    with set_context(db):
        with pytest.raises(Exception):
            x = constraint.Order(direction='left_to_right', instances=['undefined', 'M2'])
        x = constraint.Order(direction='left_to_right', instances=['M1', 'M2'])

def test_ConstraintDB_inputapi(db):
    class Garbage(constraint.PlacementConstraint):
        test: str = 'hello'
        def check(self):
            pass
    with pytest.raises(Exception):
        db.append(Garbage())

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_Order_smt_checking(db, checker):
    with set_context(db):
        x = constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3'])
        x.check(checker)
        x = constraint.Order(direction='left_to_right', instances=['M4', 'M5'])
        x.check(checker)
        x = constraint.Order(direction='left_to_right', instances=['M3', 'M2'])
        with pytest.raises(CheckerError):
            x.check(checker)

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_Order_db_append(db):
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3']))
        db.append(constraint.Order(direction='left_to_right', instances=['M4', 'M5']))
        with pytest.raises(CheckerError):
            db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))

def test_AlignInOrder_input_sanitation():
    with set_context(db):
        x = constraint.AlignInOrder(instances=['M1', 'M2'], line='top')
        x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], line='top')
        with pytest.raises(Exception):
            x = constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], line='garbage')

@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_AlignInOrder_smt_checking(db):
    with set_context(db):
        db.append(constraint.AlignInOrder(instances=['M1', 'M2', 'M3'], direction='horizontal'))
        db.append(constraint.AlignInOrder(instances=['M4', 'M5'], line='bottom'))
        with pytest.raises(CheckerError):
            db.append(constraint.AlignInOrder(instances=['M3', 'M2'], line='bottom'))


@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_AspectRatio_input_sanitation(checker, db):
    with set_context(db):
        x = constraint.AspectRatio(subcircuit="amplifier", ratio_low=0.1, ratio_high=0.5)
        x.check(checker)
        x = constraint.AspectRatio(subcircuit="amplifier", ratio_low=0.6, ratio_high=0.5)
        with pytest.raises(AssertionError):
            x.check(checker)


@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_AspectRatio_smt_checking(db):
    with set_context(db):
        db.append(constraint.AspectRatio(subcircuit="amplifier", ratio_low=0.1, ratio_high=0.5))
        with pytest.raises(CheckerError):
            db.append(constraint.AspectRatio(subcircuit="amplifier", ratio_low=0.6, ratio_high=1.0))


@pytest.mark.skipif(not Z3Checker.enabled, reason="Couldn't import Z3")
def test_ConstraintDB_incremental_checking(db):
    '''
    ConstraintDB can be used to run experiments
    using checkpoint() and revert() methods. There
    is an overhead so use sparingly
    '''
    # Experiment 1 : Success
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2', 'M3']))
    db.checkpoint()
    # Experiment 2 : Failure
    with pytest.raises(CheckerError):
        with set_context(db):
            db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))
    db.revert()
    # Experiment 3 : Success
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M4', 'M5']))
    db.checkpoint()
    # Experiment 4: Failure
    with pytest.raises(CheckerError):
        with set_context(db):
            db.append(constraint.Order(direction='left_to_right', instances=['M3', 'M2']))
    db.revert()
    # Experiment 5: Success
    with set_context(db):
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
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
    idx = db.checkpoint()
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M3']))
    db.checkpoint()
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M2', 'M3']))
    db.checkpoint()
    db.revert(idx)
    assert len(db) == 1
    assert len(db._commits) == 0
    if db._checker:
        assert 'M3' not in str(db._checker._solver)

def test_ConstraintDB_json(db):
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M3']))
    fp = pathlib.Path(__file__).parent / 'const.json'
    fp.write_text(db.json())
    with set_context(db.parent):
        newdb = constraint.ConstraintDB.parse_file(fp)
    assert db == newdb

def test_ConstraintDB_parent_relationship(db):
    with set_context(db):
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M2']))
        db.append(constraint.Order(direction='left_to_right', instances=['M1', 'M3']))
        for const in db:
            assert const.parent == db