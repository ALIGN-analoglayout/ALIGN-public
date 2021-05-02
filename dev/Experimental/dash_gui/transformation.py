
class Rect:
  def __init__( self, llx=None, lly=None, urx=None, ury=None, ll=None, ur=None):
    self.llx = ll[0] if ll is not None else llx
    self.lly = ll[1] if ll is not None else lly
    self.urx = ur[0] if ur is not None else urx
    self.ury = ur[1] if ur is not None else ury

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
    def __init__( self, *, oX=0, oY=0, sX=1, sY=1):
        self.oX = oX
        self.oY = oY
        self.sX = sX
        self.sY = sY

    def __repr__( self):
      return "Transformation(oX=%d, oY=%d, sX=%d, sY=%d)" % ( self.oX, self.oY, self.sX, self.sY) 

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
