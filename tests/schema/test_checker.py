import pytest
from align.schema.checker import Z3Checker, CheckerError

@pytest.fixture
def checker():
    return Z3Checker()

def test_single_bbox_checking(checker):
    b1 = checker.bbox_vars('M1')
    checker.append(b1.llx < b1.urx)
    with pytest.raises(CheckerError):
        checker.append(b1.urx < b1.llx)

def test_multi_bbox_checking(checker):
    b1, b2 = checker.iter_bbox_vars(['M1', 'M2'])
    checker.append(b1.llx < b1.urx)
    checker.append(b2.llx < b2.urx)
    checker.append(b2.urx <= b1.llx)
    with pytest.raises(CheckerError):
        checker.append(b1.urx <= b1.llx)