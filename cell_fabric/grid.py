from . import transformation
import copy
import collections


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

    def value( self, idx):
        assert self.n > 0
        if type(idx) is tuple:
            v = idx[0]*self.n + idx[1]
        else:
            v = idx
        whole = v // self.n
        fract = v % self.n
        assert fract in self.legalIndices
        (c,attrs) = self.grid[fract]
        period = self.grid[-1][0] - self.grid[0][0]
        c += whole*period
        return (c,attrs)

class CenteredGrid(Grid):
    def __init__( self, *, pitch, offset=0):
        super().__init__()
        self.addGridLine( offset,                     False)
        self.addGridLine( offset + pitch//2,          True)
        self.addGridLine( offset + pitch,             False)

class CenterLineGrid(Grid):
    def __init__( self):
        super().__init__()

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

    def __init__( self, *, colors, pitch, width, offset=0):
        assert len(colors) % 2 == 0
        super().__init__()
        for (idx, color) in enumerate(colors + [colors[0]]):
            self.addCenterLine( offset+idx*pitch, width, color=color)
        self.semantic()



class EnclosureGrid(Grid):
    def __init__( self, *, clg=None, pitch, offset=0, stoppoint, check=False):
        assert not check or 2*stoppoint <= pitch

        super().__init__()
        self.addGridLine( offset,                     False)
        self.addGridLine( offset + stoppoint,         True)
        self.addGridLine( offset + pitch//2,          False)
        self.addGridLine( offset + pitch - stoppoint, True)
        self.addGridLine( offset + pitch,             False)
        self.semantic()

class SingleGrid(Grid):
    def __init__( self, *, clg=None, pitch, offset=0):
        super().__init__()
        self.addGridLine( offset,         True)
        self.addGridLine( offset + pitch, True)
        self.semantic()
