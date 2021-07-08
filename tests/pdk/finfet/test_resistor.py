from align.pdk.finfet import tfr_prim, CanvasPDK
try:
    from .helper import *
except BaseException:
    from helper import *


def test_zero():
    cv = CanvasPDK()
    ox = oy = 0
    pg = tfr_prim()
    data = pg.generate(ports=['a', 'b'])
    export_to_viewer("test_tfr_0", data)
