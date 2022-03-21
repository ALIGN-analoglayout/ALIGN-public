import pathlib
import logging
from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric import Pdk, Region, SingleGrid

logger = logging.getLogger(__name__)


class CanvasPDK(DefaultCanvas):

    def __init__(self):
        self.pdk = Pdk().load(pathlib.Path(__file__).resolve().parent / 'layers.json')  # backward compatibility
        super().__init__(self.pdk, check=False)

        self.nwell = self.addGen(Region('nwell', 'Nwell',
                                        h_grid=SingleGrid(pitch=self.pdk['M2']['Pitch']),
                                        v_grid=SingleGrid(pitch=self.pdk['M1']['Pitch'])))
