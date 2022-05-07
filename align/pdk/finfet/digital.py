from .canvas import CanvasPDK
from align.schema.constraint import PlaceOnGrid, OffsetsScalings


class StandardCells(CanvasPDK):

    def __init__(self, *args, **kwargs):
        super().__init__()
        self.metadata = {'instances': []}

    def generate(self, ports, netlist_parameters=None, layout_parameters=None, *args, **kwargs):

        assert len(ports) == 4

        ch = 7
        cw = 3

        x1 = (cw+1)*self.pdk['Poly']['Pitch']
        y1 = ch*self.pdk['M2']['Pitch']
        bbox = [0, 0, x1, y1]
        t = {'layer': 'Boundary', 'netName': None, 'rect': bbox, 'netType': 'drawing'}
        self.terminals.append(t)
        self.setBboxFromBoundary()

        b_idx = (2, -1)
        e_idx = (5, 1)
        self.addWire(self.m1o, 'A', 1, b_idx, e_idx, netType="pin")
        self.addWire(self.m1o, 'O', 2, b_idx, e_idx, netType="pin")

        b_idx = (0, -1)
        e_idx = (cw, 1)
        self.addWire(self.m2o, 'VCCX', ch, b_idx, e_idx, netType="pin")
        self.addWire(self.m2o, 'VSSX', 0,  b_idx, e_idx, netType="pin")

        for i in range(4):
            self.addWire(self.m1o, None, i, (6, -1), (7, 1), netType='blockage')
            self.addWire(self.m1o, None, i, (0, -1), (1, 1), netType='blockage')

        # Additional metadata for layout post-processing
        self.metadata['instances'].append({'library': 'dig22', 'cell': 'dig22inv', 'view': 'layout'})

        poly_pitch = self.pdk['Poly']['Pitch']
        row_height = ch*self.pdk['M2']['Pitch']
        self.metadata['constraints'] = [
            PlaceOnGrid(direction='H', pitch=2*row_height,
                        ored_terms=[OffsetsScalings(offsets=[0], scalings=[1, -1])]).dict(),
            PlaceOnGrid(direction='V', pitch=poly_pitch,
                        ored_terms=[OffsetsScalings(offsets=[poly_pitch//2], scalings=[1, -1])]).dict()
        ]

        return {"bbox": bbox, "instance": {}, "terminals": self.terminals}
