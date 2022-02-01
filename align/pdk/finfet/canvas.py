import pathlib
import logging
from align.primitive.default.canvas import DefaultCanvas
from align.cell_fabric import Pdk

logger = logging.getLogger(__name__)

my_dir = pathlib.Path(__file__).resolve().parent


class CanvasPDK(DefaultCanvas):

    def __init__(self):
        self.pdk = Pdk().load(my_dir / 'layers.json')  # backward compatibility
        super().__init__(self.pdk, check=False)
