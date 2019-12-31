from canvas import FinFET14nm_Mock_PDK_Canvas
from align.cell_fabric import DefaultPrimitiveGenerator
from collections import defaultdict

import logging
logger = logging.getLogger(__name__)

class PrimitiveGenerator(FinFET14nm_Mock_PDK_Canvas, DefaultPrimitiveGenerator):

    pass