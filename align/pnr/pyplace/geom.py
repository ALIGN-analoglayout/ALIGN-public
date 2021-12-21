class Point:

  def __init__(self, x=None, y=None):
    self._x = x
    self._y = y

  def toList(self):
    return [self._x, self._y]

  def __repr__(self):
    return str(self.toList())

  def min(self, p):
    if self._x == None and self._y == None:
      return Point(p._x, p._y)
    return Point(min(self._x, p._x), min(self._y, p._y))

  def max(self, p):
    if self._x == None and self._y == None:
      return Point(p._x, p._y)
    return Point(max(self._x, p._x), max(self._y, p._y))


class Rect:

  def __init__( self, llx = None, lly = None, urx = None, ury = None):
    self._ll = Point(llx, lly)
    self._ur = Point(urx, ury)
    if (llx != None and urx != None):
      self._ll._x = min(llx, urx)
      self._ur._x = max(llx, urx)
    if (lly != None and ury != None):
      self._ll._y = min(lly, ury)
      self._ur._y = max(lly, ury)

  def bloat(self, r):
    self._ll = self._ll.min(r._ll)
    self._ur = self._ur.max(r._ur)

  def toList( self):
    return [self._ll.toList(), self._ur.toList()]

  def __str__( self):
    return str(self.toList())

  def overlaps(self, r, strict = False):
    if strict:
      return self._ll._x < r._ur._x and self._ur._x > r._ll._x and \
        self._ll._y < r._ur._y and self._ur._y > r._ll._y
    else:
      return self._ll._x <= r._ur._x and self._ur._x >= r._ll._x and \
        self._ll._y <= r._ur._y and self._ur._y >= r._ll._y

  def toString(self, unit):
    x1 = math.trunc(self._ll._x * 10000/unit)/10000
    if (x1 == math.trunc(x1)): x1 = math.trunc(x1)
    y1 = math.trunc(self._ll._y * 10000/unit)/10000
    if (y1 == math.trunc(y1)): y1 = math.trunc(y1)
    x2 = math.trunc(self._ur._x * 10000/unit)/10000
    if (x2 == math.trunc(x2)): x2 = math.trunc(x2)
    y2 = math.trunc(self._ur._y * 10000/unit)/10000
    if (y2 == math.trunc(y2)): y2 = math.trunc(y2)
    tmpstr = str(x1) + ' ' + str(y1) + ' ' + str(x2) + ' ' + str(y2)
    return tmpstr

