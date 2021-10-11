from align.pdk.finfet import tfr_prim
try:
    from .utils import export_to_viewer
except BaseException:
    from utils import export_to_viewer


def test_zero():
    pg = tfr_prim()
    data = pg.generate(ports=['a', 'b'])
    export_to_viewer("test_tfr_0", data)
