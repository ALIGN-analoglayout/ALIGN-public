import json
import pathlib
import logging
import pprint
from align.cell_fabric.canvas import Canvas
from align.cell_fabric import Wire, Via
from align.cell_fabric import CenterLineGrid, EnclosureGrid
from align.schema.pdk import LayerMetal, LayerVia, PDK

logger = logging.getLogger(__name__)


def color_closure(*, layer, generator):
    def func(term):
        pass
    return func


class NonuniformCanvas(Canvas):

    def __init__(self):
        super().__init__()
        self._define_pdk()
        self._add_generators()

    def _add_generators(self):
        for layer_name, layer in self.pdk.layers.items():
            if layer_name.startswith('M'):
                self._add_metal_generator(layer)
            elif layer_name.startswith('V'):
                self._add_via_generator(layer)

    def _add_metal_generator(self, layer):

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

    def _add_via_generator(self, layer):

        if layer.name == 'V1':
            self.postprocessor.register(layer.name, self._adjust_v1(layer=layer))

        x = 0 if self.pdk.layers[layer.stack[0]].direction =='h' else 1

        m_hor = layer.stack[x]
        m_ver = layer.stack[(x+1)%2]

        h_clg = getattr(self, m_hor).clg
        v_clg = getattr(self, m_ver).clg

        v = Via(layer.name, layer.name, h_clg=h_clg, v_clg=v_clg,
                WidthX=layer.width_x, WidthY=layer.width_y, h_ext=None, v_ext=None)

        setattr(self, layer.name, self.addGen(v))

    def _adjust_v1(self, *, layer):
        def func(term):
            return term
        return func

    def _define_pdk(self):
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
        m4 = LayerMetal(
            name="M4",
            gds_layer_number=4,
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
        m5 = LayerMetal(
            name="M5",
            gds_layer_number=5,
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
        v1 = LayerVia(
            name="V1",
            gds_layer_number=21,
            stack=('M1', 'M2'),
            width_x=600,
            width_y=500,
            space_x=1000,
            space_y=1000,
        )

        self.pdk = PDK(name=
                       """Mock FinFET technology with non-uniform metal grids.\
This PDK is for development and not functional yet.\
This file is auto-generated using tests/schema/test_pdk.py""",
                       layers={'M1': m1, 'M2': m2, 'M3': m3, 'M4': m4, 'M5': m5,
                               'V1': v1})

        my_dir = pathlib.Path(__file__).resolve().parent
        with open(my_dir / "layers.json", "wt") as fp:
            fp.write(json.dumps(self.pdk.dict(), indent=2) + '\n')
