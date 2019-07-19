import pytest
import itertools
import math

from cell_fabric import DefaultCanvas, Pdk

@pytest.fixture
def setup():
    p = Pdk().load('../../PDK_Abstraction/FinFET14nm_Mock_PDK/FinFET_Mock_PDK_Abstraction.json')
    return DefaultCanvas(p)


from collections import OrderedDict

class Stitch:

    def __init__(self, canvas):
        self.canvas = canvas
        self._c_count = 0
        self._r_count = 0

        self.components = []

    def resistor(self):
        result = f"r{self._r_count}"
        self._r_count += 1
        return result

    def capacitor(self):
        result = f"c{self._c_count}"
        self._c_count += 1
        return result

    @staticmethod
    def compute_dist(p, q):
        return abs(p - q)/1000

    def pi( self, t0, t1, R, C):
        self.components.append( (self.resistor(), t0, t1, R))
        self.components.append( (self.capacitor(), t0, 0, C/2))
        self.components.append( (self.capacitor(), t1, 0, C/2))

    def tee( self, t0, t1, R, C):
        tm = t0+t1
        self.components.append( (self.resistor(), t0, tm, R/2))
        self.components.append( (self.resistor(), tm, t1, R/2))
        self.components.append( (self.capacitor(), tm, 0, C))

    def writePex(self, fp):
        for tup in self.components:
            if tup[0][0] == 'r':
                (nm, t0, t1, v) = tup
                fp.write( f"{nm} {t0} {t1} {v}\n")
            elif tup[0][0] == 'c':
                (nm, t0, t1, v) = tup
                fp.write( f"{nm} {t0} {t1} {v}f\n")
            else:
                assert False

    def stitch(self, netcell):

        # mode = "Tee"
        mode = "Pi"

        for tup in netcell.items():
            ((t0,t1),(ly,rect)) = tup
            if ly.startswith('M'):
                dist = self.compute_dist( rect[0], rect[2]) \
                        if self.canvas.pdk[ly]['Direction'] == 'h' \
                        else self.compute_dist( rect[1], rect[3])
                (self.pi if mode == "Pi" else self.tee)( t0, t1, self.canvas.pdk[ly]['Rho']*dist, self.canvas.pdk[ly]['Kappa']*dist )
            elif ly.startswith('V'):
                self.components.append( (self.resistor(), t0, t1, self.canvas.pdk[ly]['R']))
            else:
               assert False, ly

        with open( "tests/foo.sp", "wt") as fp:
            self.writePex(fp)

def test_via_pex(setup):
    c = setup
    for (i,nm) in itertools.chain( itertools.product( [0,2,4], ['a']), itertools.product( [1,3,5], ['b'])):
        c.addWire( c.m1, nm, None, i, (0,-1), (3,-1))
    c.asciiStickDiagram( c.v1, c.m2, c.v2, c.m3, """
    +b======+=======*
                    b
+a======+=======+   |
                    |
    +b======+=======/
""")
    c.gen_data()

    netcells = c.pex.netCells
    import pprint
    pprint.pprint(netcells)

    Stitch(c).stitch(netcells)

