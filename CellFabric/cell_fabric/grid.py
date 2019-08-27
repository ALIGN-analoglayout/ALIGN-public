from . import transformation
import copy
import collections
import operator

class Grid:
    def __init__( self):
        """
        grid is a list of pairs: the grid coord and associated attributes (e.g., width, color)
"""
        self.grid = []
        self.legalIndices = set()

    def semantic( self):
        assert self.n > 0

    def addGridLine( self, value, isLegal, attrs=None):
        self.grid.append( (value, attrs))
        if isLegal:
            self.legalIndices.add( len(self.grid)-1)

    def copyShift( self, shift=None):
        result = copy.copy( self)
        if shift is not None:
            result.grid = []
            for (c,attrs) in self.grid:
                result.grid.append( (c+shift,attrs))
        return result

    @property
    def n( self):
        return len(self.grid)-1

    @property
    def period( self):
        return self.grid[-1][0] - self.grid[0][0]

    def inverseBounds( self, physical):
        (q,r) = divmod(physical - self.grid[0][0], self.period)
        last_lt = None
        ge = None
        for (idx,(c,_)) in enumerate(self.grid):
            if c - self.grid[0][0] < r:
                last_lt = idx
            else:
                ge = idx
                break
        assert ge is not None
        if physical < self.value( (q,ge), check=False)[0]:
            assert last_lt is not None
            return ((q,last_lt), (q,ge))
        else:
            return ((q,ge), (q,ge))

    def snapToLegal(self, idx, direction):
        assert len(idx) == 2
        assert len(self.legalIndices) > 0
        assert direction == 1 or direction == -1
        if direction == -1:
            op, func = operator.le, max
        else:
            op, func = operator.ge, min
        legal = { x for x in self.legalIndices if op(x, idx[1]) }
        if len(legal) > 0:
            return (idx[0], func(legal))
        else:
            return (idx[0] + direction, func(self.legalIndices))
        return idx

    def value( self, idx, check=True):
        assert self.n > 0
        v = idx[0]*self.n + idx[1] if type(idx) is tuple else idx
        (whole, fract) = divmod(v, self.n)
        if check:
            assert fract in self.legalIndices, (v, self.n, whole, fract, self.legalIndices)
        (c,attrs) = self.grid[fract]
        c += whole*self.period
        return (c,attrs)

class CenteredGrid(Grid):
    def __init__( self, *, pitch, offset=0):
        super().__init__()
        self.addGridLine( offset,                     False)
        self.addGridLine( offset + pitch//2,          True)
        self.addGridLine( offset + pitch,             False)

class CenterLineGrid(Grid):

    def addCenterLine( self, value, width, isLegal=True, *, color=None):
        assert width % 2 == 0
        self.addGridLine( value, isLegal, (width, color))

    def semantic( self):
        assert self.n > 0
        # width and color both need to be the same
        assert self.grid[0][1] == self.grid[-1][1]

class UncoloredCenterLineGrid(CenterLineGrid):

    def __init__( self, *, pitch, width, offset=0, repeat=1):
        super().__init__()
        for i in range(repeat+1):
            self.addCenterLine( offset+i*pitch, width)
        self.semantic()



class ColoredCenterLineGrid(CenterLineGrid):

    def __init__( self, *, colors, pitch, width, offset=0, repeat=None):
        assert len(colors) % 2 == 0
        super().__init__()
        if repeat is not None:
            c = (colors * repeat)[:repeat]
        else:
            c = colors
        for (idx, color) in enumerate(c + [c[0]]):
            self.addCenterLine( offset+idx*pitch, width, color=color)
        self.semantic()

class EnclosureGrid(Grid):
    def __init__( self, *, clg=None, pitch, offset=0, stoppoint, check=False):
        #assert not check or 2*stoppoint <= pitch

        super().__init__()
        self.addGridLine( offset,                     False)
        self.addGridLine( offset + stoppoint,         True)
        self.addGridLine( offset + pitch//2,          False)
        self.addGridLine( offset + pitch - stoppoint, True)
        self.addGridLine( offset + pitch,             False)
        self.semantic()

class SingleGrid(Grid):
    def __init__( self, *, clg=None, pitch, offset=0, repeat=1):
        super().__init__()
        for i in range(repeat+1):
            self.addGridLine( offset + i*pitch, True)
        self.semantic()
