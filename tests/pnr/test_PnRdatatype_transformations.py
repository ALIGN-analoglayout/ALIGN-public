from align import PnR

from align.cell_fabric import transformation

def orient2char( orient):
    if orient == PnR.Omark.FN:
        return 'FN'
    elif orient == PnR.Omark.FS:
        return 'FS'
    elif orient == PnR.Omark.N:
        return 'N'
    elif orient == PnR.Omark.S:
        return 'S'
    else:
        assert False, orient



def test_TransformBbox():

    DB = PnR.PnRdatabase()

    o = PnR.point(23,47)

    start_p = 0, 0

    p = PnR.point( *start_p)

    w,h = 100,200
    orient = PnR.Omark.S

    DB.TransformPoint( p, o, w, h, PnR.Omark.S, PnR.Forward)

    tr = transformation.Transformation.genTr( orient2char(PnR.Omark.S), w=w, h=h)
    print( tr)
    tr2 = tr.preMult( transformation.Transformation( oX=o.x, oY=o.y))
    print( tr2)

    print((p.x,p.y), tr.hit(start_p), tr2.hit(start_p))
