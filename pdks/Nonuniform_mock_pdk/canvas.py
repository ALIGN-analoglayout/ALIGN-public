import json
import pathlib
import logging
import pprint
from align.cell_fabric.canvas import Canvas
from align.cell_fabric import Wire
from align.cell_fabric import CenterLineGrid, EnclosureGrid
from align.schema.pdk import LayerMetal, PDK

logger = logging.getLogger(__name__)


def color_closure(*, layer, generator):
    def func(term):
        pass
    return func


class NonuniformCanvas(Canvas):

    def _define_canvas(self):
        m1 = LayerMetal(
            name="M1",
            gds_layer_number=1,
            direction="v",
            min_length=1000,
            min_end_to_end=400,
            offset=0,
            width=[600],
            space=[400],
            stop_pitch=1000,
            stop_point=200,
            stop_offset=0
        )

        m2 = LayerMetal(
            name="M2",
            gds_layer_number=2,
            direction="h",
            min_length=500,
            min_end_to_end=300,
            offset=0,
            width=[400, 500, 500, 600, 600, 500, 500],
            space=[300, 300, 400, 400, 400, 300, 300],
            stop_pitch=1000,
            stop_point=350,
            stop_offset=0,
        )

        m3 = LayerMetal(
            name="M3",
            gds_layer_number=3,
            direction="v",
            min_length=1000,
            min_end_to_end=400,
            offset=0,
            width=[800, 1000],
            space=[600, 600],
            color=["a", "b"],
            stop_pitch=1000,
            stop_point=500,
            stop_offset=0
        )

        self.pdk = PDK(name=
                       """Mock FinFET technology with non-uniform metal grids.\
This PDK is for development and not functional yet.\
This file is auto-generated using tests/schema/test_pdk.py""",
                       layers=[m1, m2, m3])

        # pprint.pprint(self.pdk.dict())

        my_dir = pathlib.Path(__file__).resolve().parent
        with open(my_dir / "layers.json", "wt") as fp:
            fp.write(json.dumps(self.pdk.dict(), indent=2) + '\n')

    def __init__(self):
        super().__init__()
        self._define_canvas()
        self._create_metal_canvas()

    def _create_metal_canvas(self):
        for layer in self.pdk.layers:
            if layer.name.startswith('M'):
                self._create_metal(layer)

    def _create_metal(self, layer):

        m = Wire(layer.name, layer.name, layer.direction, clg=None, spg=None)

        index = layer.offset
        m.clg = CenterLineGrid()
        m.clg.addCenterLine(index, layer.width[0], isLegal=True,
                            color=None if layer.color is None else layer.color[0])
        for i in range(1, len(layer.width)):
            index += (layer.width[i-1] + layer.width[i])//2 + layer.space[i-1]
            m.clg.addCenterLine(index, layer.width[i], isLegal=True,
                                color=None if layer.color is None else layer.color[i])

        i = len(layer.width) - 1
        index += (layer.width[i] + layer.width[0])//2 + layer.space[i]
        m.clg.addCenterLine(index, layer.width[0], isLegal=True,
                            color=None if layer.color is None else layer.color[0])
        m.clg.semantic()

        m.spg = EnclosureGrid(pitch=layer.stop_pitch,
                              offset=layer.stop_offset,
                              stoppoint=layer.stop_point,
                              check=True)

        setattr(self, layer.name, self.addGen(m))

        if layer.color is not None:
            self.postprocessor.register(layer.name, color_closure(layer=layer, generator=m))
