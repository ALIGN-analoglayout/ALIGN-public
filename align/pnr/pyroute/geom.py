import math

class Point:
    def __init__(self, x = 0, y = 0):
        self._x = x
        self._y = y
    def __str__(self): return f'Point({self._x}, {self._y})'
    def __repr__(self): return f'Point({self._x}, {self._y})'

    def transform(self, tr):
        return Point(tr._or._x + tr._sX * self._x, tr._or._y + tr._sY * self._y)

    def moveto(self, x, y):
        self._x = x
        self._y = y

    def moveby(self, dx, dy):
        self._x += dx
        self._y += dy

    def min(self, p):
        if self._x == None and self._y == None:
            return Point(p._x, p._y)
        return Point(min(self._x, p._x), min(self._y, p._y))

    def max(self, p):
        if self._x == None and self._y == None:
            return Point(p._x, p._y)
        return Point(max(self._x, p._x), max(self._y, p._y))


class Rect:
    def __init__(self, ll = None, ur = None):
        self._ll = ll if ll else Point(math.inf, math.inf)
        self._ur = ur if ur else Point(-math.inf, -math.inf)
        if ll and ur: self.fix()

    def __str__(self): return f'[{self._ll},{self._ur}]'
    def __repr__(self): return f'Rect({self._ll}, {self._ur})'

    def fix(self):
        if self._ll._x > self._ur._x:
            self._ll._x, self._ur._x = self._ur._x, self._ll._x
        if self._ll._y > self._ur._y:
            self._ll._y, self._ur._y = self._ur._y, self._ll._y

    def transform(self, tr):
        r = Rect(self._ll.transform(tr), self._ur.transform(tr))
        return r

    def merge(self, r):
        self._ll._x = min(self._ll._x, r._ll._x)
        self._ll._y = min(self._ll._y, r._ll._y)
        self._ur._x = max(self._ur._x, r._ur._x)
        self._ur._y = max(self._ur._y, r._ur._y)

    def xmin(self): return self._ll._x
    def ymin(self): return self._ll._y
    def xmax(self): return self._ur._x
    def ymax(self): return self._ur._y

    def xcenter(self): return (self._ll._x + self._ur._x) / 2
    def ycenter(self): return (self._ll._y + self._ur._y) / 2

    def width(self): return self._ur._x - self._ll._x

    def height(self): return self._ur._y - self._ll._y

    def moveby(self, dx, dy):
        self._ll.moveby(dx, dy)
        self._ur.moveby(dx, dy)

    def moveto(self, x, y):
        self._ur.moveby(x - self._ll._x, y - self._ll._y)
        self._ll.moveto(x, y)

    def overlapinx(self, r, strict = False):
        if strict:
            return self._ll._x < r._ur._x and self._ur._x > r._ll._x
        return self._ll._x <= r._ur._x and self._ur._x >= r._ll._x

    def overlapiny(self, r, strict = False):
        if strict:
            return self._ll._y < r._ur._y and self._ur._y > r._ll._y
        return self._ll._y <= r._ur._y and self._ur._y >= r._ll._y

    def overlap(self, r, strict = False):
        return self.overlapinx(r, strict) and self.overlapiny(r, strict)

    def bloat(self, r):
        self._ll = self._ll.min(r._ll)
        self._ur = self._ur.max(r._ur)


class Transform:
    def __init__(self, oX = 0, oY = 0, sX = 1, sY = 1):
        self._or = Point(oX, oY) 
        self._sX = sX
        self._sY = sY
    def __str__(self): return f'({self._or} {self._sX} {self._sY})'
    def __repr__(self): return f'Transform({self._or._x}, {self._or._y}, {self._sX}, {self._sY})'


    def apply(self, tr = None):
        if tr:
            self._or = Point(tr._or._x + self._or._x * tr._sX, tr._or._y + self._or._y * tr._sY)
            self._sX *= tr._sX
            self._sY *= tr._sY

    def orient(self):
        if (self._sX == 1 and self._sY == 1): return "N"
        if (self._sX == -1 and self._sY == 1): return "FN"
        if (self._sX == 1 and self._sY == -1): return "FS"
        return "S";
        


