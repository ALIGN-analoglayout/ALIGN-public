from align.schema.transistor import Transistor
from .canvas import CanvasPDK


class MOS(CanvasPDK):


    def __init__(self):
        super().__init__()
        self.height   = 14
        self.diff_idx = 8


    def mos(self, tx: Transistor, track_pattern=None):

        assert tx.nf % 2 == 0, f'Odd number of fingers are not allowed'
        
        assert tx.nfin > 0 and tx.nfin < 9, f'Transistor width not supported {tx.w}'

        self.tx = tx

        if tx.nfin < 7:
            ds_b_idx = (1, -1)
        else:
            ds_b_idx = (0, -1)

        if tx.device_type == 'stack':
            self.addWire(self.m1, 'S', 'S', 1,       ds_b_idx, (4, 1))
            self.addWire(self.m1, 'D', 'D', 1+tx.nf, ds_b_idx, (4, 1))
        else:
            for x in range(1, 2+tx.nf):
                p = 'D' if x % 2 == 0 else 'S'
                self.addWire(self.m1, p, p, x, ds_b_idx, (4, 1))

        for x in range(2, 1+tx.nf, 2):
            self.addWire(self.m1,  'G', 'G',  x, (5, -1), (6, 1))

        if track_pattern is not None:

            if 'G' in track_pattern:
                for y in track_pattern['G']:
                    if tx.nf > 2:
                        g_b_idx = (2, -1)
                        g_e_idx = (tx.nf, 1)
                    else:
                        g_b_idx = (1, -1)
                        g_e_idx = (1+tx.nf, 1)
                    self.addWire(self.m2, 'G', 'G',  y, g_b_idx, g_e_idx)

            if tx.device_type == 'stack':
                s_b_idx = (1, -1)
                s_e_idx = (2,  1)
                d_b_idx = (tx.nf, -1)
                d_e_idx = (1+tx.nf,  1)
            else:
                s_b_idx = (1, -1)
                s_e_idx = (1+tx.nf,  1)
                d_b_idx = (1, -1)
                d_e_idx = (1+tx.nf,  1)

            if 'S' in track_pattern:
                for y in track_pattern['S']:
                    self.addWire(self.m2, 'S', 'S',  y, s_b_idx, s_e_idx)

            if 'D' in track_pattern:
                for y in track_pattern['D']:
                    self.addWire(self.m2, 'D', 'D',  y, d_b_idx, d_e_idx)

            self.drop_via(self.v1)

        # # DEBUG VISUAL AID
        # for y in range(8):
        #     self.addWire(self.m2, None, None, y, (1, -1), (3, 1))

        # Precomputed bounding box
        x1 = self.pdk['Poly']['Pitch']*(2+self.tx.nf)
        y1 = self.pdk['M2']['Pitch']*(self.height//2)
        bbox = [0, 0, x1, y1]

        return {"bbox": bbox, "instance": {}, "terminals": self.terminals}


    def tap(self, tx: Transistor):
        
        assert tx.nf % 2 == 0, f'Odd number of fingers are not allowed'

        self.tx = tx

        if self.tx.model_name.startswith('n'):
            # M1/M2
            for x in range(1, 2+tx.nf, 2):
                self.addWire(self.m1, 'B', 'B', x, (1, -1), (6, 1))
            self.addWire(self.m2, 'B', 'B', 2, (1, -1), (1+tx.nf, 1))
            self.drop_via(self.v1)

        else:
            # M1/M2
            for x in range(1, 2+tx.nf, 2):
                self.addWire(self.m1, 'B', 'B', x, (1, -1), (6, 1))
            self.addWire(self.m2, 'B', 'B', 4, (1, -1), (1+tx.nf, 1))
            self.drop_via(self.v1)

        # # DEBUG VISUAL AID
        # for y in range(8):
        #     self.addWire(self.m2, None, None, y, (1, -1), (3, 1))

        # Precomputed bounding box
        x1 = self.pdk['Poly']['Pitch']*(2+self.tx.nf)
        y1 = self.pdk['M2']['Pitch']*(self.height//2)
        bbox = [0, 0, x1, y1]

        return {"bbox": bbox, "instance": {}, "terminals": self.terminals}


    def fill(self, nf, nfin):

        # Precomputed bounding box
        x1 = self.pdk['Poly']['Pitch']*nf
        y1 = self.pdk['M2']['Pitch']*(self.height//2)
        bbox = [0, 0, x1, y1]

        return {"bbox": bbox, "instance": {}, "terminals": self.terminals}
