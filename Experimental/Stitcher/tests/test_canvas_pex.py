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
    
    def __init__(self):
        self.c_count = 0
        self.r_count = 0

        self.rho = { "metal1": 100.0,
                     "metal2": 60.0,
                     "metal3": 40.0}

        self.kappa = { "metal1": 0.2,
                       "metal2": 0.2,
                       "metal3": 0.2}

        self.r = { "via1": 50.0, "via2": 50.0}

        self.components = []


    def resistor(self):
        result = f"r{self.r_count}"
        self.r_count += 1
        return result

    def capacitor(self):
        result = f"c{self.c_count}"
        self.c_count += 1
        return result

    def lumped( self, ly, rect):
        def compute_dist(p, q):
            return abs(p - q)/1000

        if   ly in ["metal2"]:
            dist = compute_dist( rect[0], rect[2])
            return (self.rho[ly]*dist,self.kappa[ly]*dist)
        elif ly in ["metal1","metal3"]:
            dist = compute_dist( rect[1], rect[3])
            return (self.rho[ly]*dist,self.kappa[ly]*dist)
        elif ly in ["via1","via2"]:
            return (self.r[ly],)
        else:
            assert False, ly


    def pi( self, t0, t1, pair):
        self.components.append( (self.resistor(), t0, t1, pair[0]))
        self.components.append( (self.capacitor(), t0, 0, pair[1]/2))
        self.components.append( (self.capacitor(), t1, 0, pair[1]/2))
        
    def tee( self, t0, t1, pair):
        tm = t0+t1
        self.components.append( (self.resistor(), t0, tm, pair[0]/2))
        self.components.append( (self.resistor(), tm, t1, pair[0]/2))
        self.components.append( (self.capacitor(), tm, 0, pair[1]))


    def stitch(self, netcell):

    #    mode = "Tee"
        mode = "Pi"

        for tup in netcell.items():
            ((t0,t1),(ly,rect)) = tup
            ly = { 'M1': "metal1", 'M2': "metal2", 'M3': "metal3", 'V1': "via1", 'V2': "via2"}[ly]
            pair = self.lumped(ly,rect)
            if ly in ["metal1","metal2","metal3"]:
                (self.pi if mode == "Pi" else self.tee)( t0, t1, pair)
            elif ly in ["via1","via2"]:
                self.components.append( (self.resistor(), t0, t1, pair[0]))
            else:
               assert False, ly

        with open( "tests/foo.sp", "wt") as fp:

          for tup in self.components:
            if tup[0][0] == 'r': 
                (nm, t0, t1, v) = tup
                fp.write( f"{nm} {t0} {t1} {v}\n")
            elif tup[0][0] == 'c':
                (nm, t0, t1, v) = tup
                fp.write( f"{nm} {t0} {t1} {v}f\n")
            else:
                assert False


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

    Stitch().stitch(netcells)

