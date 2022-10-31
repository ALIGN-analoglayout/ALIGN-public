import pathlib
import logging
from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric import Pdk, Region, SingleGrid, Wire, Via

logger = logging.getLogger(__name__)


class CanvasPDK(DefaultCanvas):

    def __init__(self):
        self.pdk = Pdk().load(pathlib.Path(__file__).resolve().parent / 'layers.json')  # backward compatibility
        super().__init__(self.pdk, check=False)

        self.nwell = self.addGen(Region('nwell', 'Nwell',
                                        h_grid=SingleGrid(pitch=self.pdk['M2']['Pitch']),
                                        v_grid=SingleGrid(pitch=self.pdk['M1']['Pitch'])))

        for layer in ["m1", "m2", "m3"]:
            wire = getattr(self, layer)
            spg_offset = clg_offset = 0
            if wire.direction == 'v':
                clg_offset = self.pdk['Poly']['Pitch']//2
            else:
                spg_offset = self.pdk['Poly']['Pitch']//2

            setattr(self, f"{layer}o", Wire(wire.nm, wire.layer, wire.direction,
                                            clg=wire.clg.copyShift(clg_offset),
                                            spg=wire.spg.copyShift(spg_offset)))

        # VT
        self.vt = self.addGen(Via('vt', 'VT', h_clg=self.m2.clg, v_clg=self.m1.clg, WidthX=self.pdk['VT']['WidthX'], WidthY=self.pdk['VT']['WidthY']))
