from align.pdk.finfet import tfr_prim, CanvasPDK
try:
    from .helper import *
except:
    from helper import *


def test_zero():
    cv = CanvasPDK()
    ox = oy = 0
    pg = tfr_prim()
    data = pg.generate()
    export_to_viewer("test_tfr_0", data)

