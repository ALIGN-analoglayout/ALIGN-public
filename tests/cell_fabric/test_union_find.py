
from align.cell_fabric.remove_duplicates import UnionFind

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

def test_big():
    n = 50000
    lst = [ UnionFind() for i in range(n)]
    last = None
    for uf in lst:
        if last is not None:
            uf.connect(last)
        last = uf
    q = lst[0].root()
    for uf in lst:
        assert uf.root() == q
