from .canvas import CanvasPDK


class tfr_prim(CanvasPDK):
    
    def __init__(self, *args, **kwargs):
        super().__init__()
        self.instantiated_cells = []

    def generate(self):

        b_idx = (4, -1)
        e_idx = (7, -1)

        self.addWire(self.m2, 'a', 'a', 12, b_idx, e_idx)
        self.addWire(self.m2, 'b', 'b',  2, b_idx, e_idx)

        x1 = self.pdk['Poly']['Pitch']*(10)
        y1 = self.pdk['M2']['Pitch']*(14)
        bbox = [0, 0, x1, y1]

        t = {'layer': 'Boundary', 'netName': None, 'rect': bbox}
        self.terminals.append(t)

        return {"bbox": bbox, "instance": {}, "terminals": self.terminals}
