from .canvas import CanvasPDK
from align.schema.constraint import PlaceOnGrid, OffsetsScalings


class tfr_prim(CanvasPDK):

    def __init__(self, *args, **kwargs):
        super().__init__()
        self.metadata = {'instances': []}

    def generate(self, ports, netlist_parameters=None, layout_parameters=None, *args, **kwargs):

        assert len(ports) == 2

        b_idx = (4, -1)
        e_idx = (7, -1)

        if netlist_parameters is None:
            netlist_parameters = dict()

        p1 = netlist_parameters.get('P1', 'SIG')
        if p1 == 'SIG':
            self.addWire(self.m2, ports[0], 12, b_idx, e_idx, netType="pin")
        p2 = netlist_parameters.get('P2', 'SIG')
        if p2 == 'SIG':
            self.addWire(self.m2, ports[1], 2, b_idx, e_idx, netType="pin")

        x1 = self.pdk['Poly']['Pitch']*(10)
        y1 = self.pdk['M2']['Pitch']*(14)
        bbox = [0, 0, x1, y1]

        t = {'layer': 'Boundary', 'netName': None, 'rect': bbox, 'netType': 'drawing'}
        self.terminals.append(t)

        # Additional metadata for layout post-processing
        self.metadata['instances'].append({'sample_key': 'sample_value'})

        poly_pitch = self.pdk['Poly']['Pitch']
        row_height = self.pdk['M2']['Pitch']*7
        self.metadata['constraints'] = [
            PlaceOnGrid(direction='H', pitch=2*row_height, ored_terms=[OffsetsScalings(offsets=[1*row_height], scalings=[1])]).dict(),
            PlaceOnGrid(direction='V', pitch=5*poly_pitch, ored_terms=[OffsetsScalings(offsets=[1*poly_pitch], scalings=[1])]).dict()
        ]
        return {"bbox": bbox, "instance": {}, "terminals": self.terminals, "metadata": self.metadata}
