import pytest
from cell_fabric.remove_duplicates import UnionFind

def test_three():
    x = UnionFind()
    y = UnionFind()
    z = UnionFind()

    assert x.root() != y.root()
    assert x.root() != z.root()
    assert y.root() != z.root()

    x.connect(y)

    assert x.root() == y.root()
    assert x.root() != z.root()
    assert y.root() != z.root()

    x.connect(z)

    assert x.root() == y.root()
    assert x.root() == z.root()
    assert y.root() == z.root()
