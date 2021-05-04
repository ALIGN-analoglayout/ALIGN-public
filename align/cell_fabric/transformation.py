
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
    @staticmethod
    def genTr( tag, *, w, h):
      if   tag == "FN":
          tr = Transformation( oX=w,        sX=-1       )
      elif tag == "FS":
          tr = Transformation(        oY=h,        sY=-1)
      elif tag == "N":
          tr = Transformation(                           )
      elif tag == "S":
          tr = Transformation( oX=w, oY=h, sX=-1, sY=-1)
      else:
          assert tag in ["FN","FS","N","S"]
      return tr

    def __init__( self, oX=0, oY=0, sX=1, sY=1):
        self.oX = oX
        self.oY = oY
        self.sX = sX
        self.sY = sY

    def __repr__( self):
      return "Transformation(oX=%d, oY=%d, sX=%d, sY=%d)" % ( self.oX, self.oY, self.sX, self.sY) 

    def toTuple(self):
      return self.oX, self.oY, self.sX, self.sY

    def toDict(self):
      return { 'oX':self.oX, 'oY':self.oY, 'sX':self.sX, 'sY':self.sY}

    def __eq__(self, other):
      return self.toTuple() == other.toTuple()

    def __hash__(self):
      return self.toTuple().__hash__()

    def hit( self, p):
        x,y = p
        return self.sX * x + self.oX, self.sY * y + self.oY

    def hitRect( self, r):
        llx,lly = self.hit( (r.llx, r.lly))
        urx,ury = self.hit( (r.urx, r.ury))
        return Rect( llx, lly, urx, ury)

    def inv(self):
        # A.sX 0    A.oX     B.sX 0    B.oX      1 0 0
        # 0    A.sY A.oY     0    B.sY B.oY      0 1 0
        # 0    0    1        0    0    1         0 0 1
        #
        # A.sX = B.sX
        # A.sY = B.sY
        # A.sX B.oX + A.oX = 0
        # A.sY B.oY + A.oY = 0
        # =>
        # B.oX = -A.oX / A.sX = -A.oX * A.sX
        # B.oY = -A.oY / A.sY = -A.oY * A.sY
        return Transformation( sX=self.sX,          sY=self.sY,
                               oX=-self.oX*self.sX, oY=-self.oY*self.sY)


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
