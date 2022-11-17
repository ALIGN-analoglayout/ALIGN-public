import pathlib
import logging
from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric import Pdk

logger = logging.getLogger(__name__)


class CanvasPDK(DefaultCanvas):
    def __init__(self):
        self.pdk = Pdk().load(pathlib.Path(__file__).resolve().parent / 'layers.json')  # backward compatibility
        super().__init__(self.pdk, check=False)


class MOSGenerator(CanvasPDK):
    def __init__(self, *args, **kwargs):
        super().__init__()
