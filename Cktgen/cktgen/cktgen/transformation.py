class Tech:
# Mock the tech file to temporarily simplify integration
  def __init__( self):
      self.halfXADTGrid = 1
      self.halfYADTGrid = 1
      self.halfXGRGrid = 2
      self.halfYGRGrid = 2
      self.pitchPoly   = 720
      self.pitchDG     = 720
      self.verticalMetals = ["metal1","metal3","metal5"]
      self.horizontalMetals = ["metal2","metal4"]

class Rect:
  def __init__( self, llx=None, lly=None, urx=None, ury=None):
      self.llx = llx
      self.lly = lly
      self.urx = urx
      self.ury = ury

  def canonical( self):
      [llx,lly,urx,ury] = self.toList()
      if llx > urx: llx,urx = urx,llx
      if lly > ury: lly,ury = ury,lly
      return Rect( llx,lly,urx,ury)

  def toList( self):
      return [self.llx, self.lly, self.urx, self.ury]

  def __repr__( self):
    return str(self.toList())

class Transformation:
    def __init__( self, oX=0, oY=0, sX=1, sY=1):
        self.oX = oX
        self.oY = oY
        self.sX = sX
        self.sY = sY

    def __repr__( self):
      return "oX: %d oY: %d sX: %d sY: %d" % ( self.oX, self.oY, self.sX, self.sY) 

    def __eq__( self, other):
      return other is not None and self.oX == other.oX and self.oY == other.oY and self.sX == other.sX and self.sY == other.sY

    def plusOneIfMirrored( self):
      xx = 1 if self.sX == -1 else 0
      yy = 1 if self.sY == -1 else 0
      return Transformation( self.oX+xx, self.oY+yy, self.sX, self.sY)

    def hit( self, p):
        x,y = p
        return self.sX * x + self.oX, self.sY * y + self.oY

    def hitRect( self, r):
        llx,lly = self.hit( (r.llx, r.lly))
        urx,ury = self.hit( (r.urx, r.ury))
        return Rect( llx, lly, urx, ury)

    @staticmethod
    def mult( A, B):
        # A.sX 0    A.oX     B.sX 0    B.oX
        # 0    A.sY A.oY     0    B.sY B.oY
        # 0    0    1        0    0    1
        C = Transformation()
        C.sX = A.sX * B.sX
        C.sY = A.sY * B.sY
        C.oX = A.sX * B.oX + A.oX
        C.oY = A.sY * B.oY + A.oY
        return C

    def preMult( self, A):
      return self.__class__.mult( A, self)

    def postMult( self, A):
      return self.__class__.mult( self, A)

def test_transformation_hit0():
    t = Transformation( 0, 10)
    assert (0,10) == t.hit( (0,0))

def test_transformation_hit1():
    t = Transformation( 0, 10, 1, -1)
    assert (0,0) == t.hit( (0,10))

def test_transformation_Mult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (Transformation.mult( b, a)).hit( (0,0))

def test_transformation_preMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (a.preMult(b)).hit( (0,0))

def test_transformation_postMult0():
    a = Transformation( 0, 10, 0, 0)
    b = Transformation( 0,  0, 1,-1)
    assert (0,-10) == (b.postMult(a)).hit( (0,0))
