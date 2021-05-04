import pytest

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

def test_TransformPointForward():

    DB = PnR.PnRdatabase()

    o = PnR.point(23,47)

    start_p = 42, -18

    w,h = 100,200

    for orient in [ PnR.Omark.N, PnR.Omark.S, PnR.Omark.FN, PnR.Omark.FS]:
        p = PnR.point( *start_p)
        DB.TransformPoint( p, o, w, h, orient, PnR.Forward)

        tr = transformation.Transformation.genTr( orient2char(orient), w=w, h=h)
        tr.oX, tr.oY = 0, 0
        # tr is now just the flipping matrix, no translation

        tr_offset = transformation.Transformation( oX=o.x, oY=o.y)

        tr_center = transformation.Transformation( oX=-w//2, oY=-h//2)
        tr_uncenter = transformation.Transformation( oX=w//2, oY=h//2)        
        tr_first = tr_uncenter.postMult( tr).postMult( tr_center)
        tr_whole = tr_offset.postMult( tr_first)

        tr_first2 = transformation.Transformation.genTr( orient2char(orient), w=w, h=h)
        tr_whole2 = tr_offset.postMult( tr_first2)

        assert transformation.Transformation() == tr_first2.postMult( tr_first2.inv())
        assert transformation.Transformation() == tr_first2.inv().postMult( tr_first2)

        assert tr_first == tr_first2
        assert tr_whole == tr_whole2

        print(tr_first, tr_first2)
        #print(tr_whole, tr_whole2)

        p_shadow = tr_whole.hit( start_p)
        assert (p.x,p.y) == p_shadow

def test_TransformPointBackward():

    DB = PnR.PnRdatabase()

    o = PnR.point(23,47)

    start_p = 42, -18

    w,h = 100,200

    for orient in [ PnR.Omark.N, PnR.Omark.S, PnR.Omark.FN, PnR.Omark.FS]:
        p = PnR.point( *start_p)
        DB.TransformPoint( p, o, w, h, orient, PnR.Backward)

        tr = transformation.Transformation.genTr( orient2char(orient), w=w, h=h)
        tr.oX, tr.oY = 0, 0
        # tr is now just the flipping matrix, no translation

        tr_offset = transformation.Transformation( oX=o.x, oY=o.y)

        tr_center = transformation.Transformation( oX=-w//2, oY=-h//2)
        tr_uncenter = transformation.Transformation( oX=w//2, oY=h//2)        
        tr_first = tr_uncenter.postMult( tr).postMult( tr_center)
        tr_whole = tr_offset.postMult( tr_first)

        assert tr_first.inv() == tr_center.inv().postMult( tr.inv()).postMult( tr_uncenter.inv())
        assert tr_first.inv() == tr_uncenter.postMult( tr).postMult( tr_center)
        assert tr_first.inv() == tr_first

        assert tr_whole.inv() == tr_first.inv().postMult( tr_offset.inv())

        
        tr_first2 = transformation.Transformation.genTr( orient2char(orient), w=w, h=h)

        tr_whole2 = tr_offset.postMult( tr_first2)

        assert tr_first == tr_first2
        assert tr_whole == tr_whole2

        print(tr_first, tr_first2)
        #print(tr_whole, tr_whole2)

        p_shadow = tr_whole.inv().hit( start_p)
        assert (p.x,p.y) == p_shadow


def test_TransformBbox():

    DB = PnR.PnRdatabase()

    o = PnR.point(23,47)

    LL_p = 42, -18
    UR_p = LL_p[0]+10, LL_p[1]+20

    w,h = 100,200

    for direction in [PnR.Forward, PnR.Backward]:
        for orient in [ PnR.Omark.N, PnR.Omark.S, PnR.Omark.FN, PnR.Omark.FS,
                        PnR.Omark.E, PnR.Omark.W, PnR.Omark.FE, PnR.Omark.FW]:
            LL, UR = PnR.point( *LL_p), PnR.point( *UR_p)
            bbox = PnR.bbox( LL, UR)

            DB.TransformBbox( bbox, o, w, h, orient, direction)
            DB.TransformPoint( LL, o, w, h, orient, direction)
            DB.TransformPoint( UR, o, w, h, orient, direction)

            canonical_LL = min(LL.x,UR.x), min(LL.y,UR.y) 
            canonical_UR = max(LL.x,UR.x), max(LL.y,UR.y) 

            assert (bbox.LL.x,bbox.LL.y) == canonical_LL 
            assert (bbox.UR.x,bbox.UR.y) == canonical_UR
