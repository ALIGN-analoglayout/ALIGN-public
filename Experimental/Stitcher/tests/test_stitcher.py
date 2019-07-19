
from collections import OrderedDict

class Stitch:
    
    def __init__(self):
        self.c_count = 0
        self.r_count = 0

        self.rho = { "metal2": 60.0,
                     "metal3": 40.0}

        self.kappa = { "metal2": 0.2,
                       "metal3": 0.2}

        self.r = { "via2": 50.0}

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
            return abs(p - q)/10000

        if   ly in ["metal2"]:
            dist = compute_dist( rect[0], rect[2])
            return (self.rho[ly]*dist,self.kappa[ly]*dist)
        elif ly in ["metal3"]:
            dist = compute_dist( rect[1], rect[3])
            return (self.rho[ly]*dist,self.kappa[ly]*dist)
        elif ly in ["via2"]:
            return (self.r[ly],)
        else:
            assert False


    def pi( self, t0, t1, pair):
        self.components.append( (self.resistor(), t0, t1, pair[0]))
        self.components.append( (self.capacitor(), t0, 0, pair[1]/2))
        self.components.append( (self.capacitor(), t1, 0, pair[1]/2))
        
    def tee( self, t0, t1, pair):
        tm = t0+t1
        self.components.append( (self.resistor(), t0, tm, pair[0]/2))
        self.components.append( (self.resistor(), tm, t1, pair[0]/2))
        self.components.append( (self.capacitor(), tm, 0, pair[1]))


    def stitch(self):
        netcell = OrderedDict([
            ("a", [ ("a:1", "a:2", "metal3", [0,     0,     0, 10000]),
                   ("a:2","a:3", "via2",     [0, 10000,     0, 10000]),
                   ("a:3", "a:4", "metal2",  [0, 10000, 10000, 10000])
                  ]
            )
            ])

        mode = "Tee"
    #    mode = "Pi"

        for net,lst in netcell.items():
            for tup in lst:
                (t0,t1,ly,rect) = tup
                pair = self.lumped(ly,rect)
                if ly in ["metal2","metal3"]:
                    (self.pi if mode == "Pi" else self.tee)( t0, t1, pair)
                elif ly in ["via2"]:
                    self.components.append( (self.resistor(), t0, t1, pair[0]))
                else:
                   assert False

        for tup in self.components:
            if tup[0][0] == 'r': 
                (nm, t0, t1, v) = tup
                print( f"{nm} {t0} {t1} {v}")
            elif tup[0][0] == 'c':
                (nm, t0, t1, v) = tup
                print( f"{nm} {t0} {t1} {v}")
            else:
                assert False

def test_one():
    Stitch().stitch()
