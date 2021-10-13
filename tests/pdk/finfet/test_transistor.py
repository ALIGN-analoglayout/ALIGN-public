from align.schema.transistor import Transistor
from align.pdk.finfet import MOS, CanvasPDK
try:
    from .utils import compare_with_golden, place
except BaseException:
    from utils import compare_with_golden, place


def test_zero():
    cv = CanvasPDK()
    ox = oy = 0
    track_pattern = {'G': [6], 'S': [4], 'D': [2]}
    for nfin in range(1, 9):
        ox = 0
        for model_name in ['n', 'p']:
            for device_type in ["stack", "parallel"]:
                for nf in [2, 4, 6]:
                    mg = MOS()
                    tx = Transistor(model_name=model_name, nf=nf, nfin=nfin, device_type=device_type)
                    data = mg.mos(tx, track_pattern=track_pattern)
                    place(cv, data, ox, oy)
                    ox += data['bbox'][2]
        oy += data['bbox'][3]
    compare_with_golden("test_transistor_0", cv)
