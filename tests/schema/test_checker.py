import pytest
from align.schema.checker import Z3Checker

@pytest.fixture
def checker():
    return Z3Checker()

@pytest.mark.skipif(not Z3Checker.enabled, reason="requires z3")
def test_single_bbox_checking(checker):
    b1 = checker.bbox('M1')[0]
    checker.append(b1.llx < b1.urx)
    with pytest.raises(AssertionError):
        checker.append(b1.urx < b1.llx)

@pytest.mark.skipif(not Z3Checker.enabled, reason="requires z3")
def test_multi_bbox_checking(checker):
    b1, b2 = checker.bbox('M1', 'M2')
    checker.append(b1.llx < b1.urx)
    checker.append(b2.llx < b2.urx)
    checker.append(b2.urx <= b1.llx)
    with pytest.raises(AssertionError):
        checker.append(b1.urx <= b1.llx)