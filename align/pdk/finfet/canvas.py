import json
import pathlib
import logging
from align.cell_fabric.canvas import Canvas
from align.cell_fabric import Wire, Via, Region
from align.cell_fabric import CenterLineGrid, EnclosureGrid, SingleGrid
from align.schema.pdk import LayerMetal, LayerVia, LayerViaSet, PDK
from align.cell_fabric import Pdk

logger = logging.getLogger(__name__)

my_dir = pathlib.Path(__file__).resolve().parent


def color_closure(*, layer, generator):
    def func(term):
        return term
    return func


class CanvasPDK(Canvas):

    def __init__(self):
        pdk = Pdk().load(my_dir / 'layers.json')  # backward compatibility
        super().__init__(pdk)
        self._define_pdk()
        self._add_generators()

    def _add_generators(self):
        # This PDK only has metal stack
        for layer_name, layer in self.pdk_v2.layers.items():
            if layer_name.startswith('M'):
                self._add_metal_generator(layer)
            elif layer_name.startswith('V'):
                self._add_via_generator(layer.default_via)

        v_grid_pitch = sum(self.pdk_v2.layers['M1'].width) + sum(self.pdk_v2.layers['M1'].space)
        h_grid_pitch = sum(self.pdk_v2.layers['M2'].width) + sum(self.pdk_v2.layers['M2'].space)
        setattr(self, 'boundary', self.addGen(Region('boundary', 'Boundary',
                                               h_grid=SingleGrid(pitch=h_grid_pitch),
                                               v_grid=SingleGrid(pitch=v_grid_pitch))))

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

        setattr(self, layer.name.lower(), self.addGen(m))

        if layer.color is not None:
            self.postprocessor.register(layer.name, color_closure(layer=layer, generator=m))

    def _add_via_generator(self, layer):

        x = 0 if self.pdk_v2.layers[layer.stack[0]].direction =='h' else 1

        m_hor = layer.stack[x]
        m_ver = layer.stack[(x+1)%2]

        h_clg = self.generators[m_hor].clg
        v_clg = self.generators[m_ver].clg

        v = Via(layer.name, layer.name, h_clg=h_clg, v_clg=v_clg,
                WidthX=layer.width_x, WidthY=layer.width_y, h_ext=None, v_ext=None)

        setattr(self, layer.name.lower(), self.addGen(v))

    def _define_pdk(self):
        m1 = LayerMetal(
            name="M1",
            gds_layer_number=1,
            direction="v",
            min_length=1300, min_end_to_end=500,
            offset=0, width=[600], space=[480], stop_pitch=900, stop_point=200, stop_offset=0
        )
        m2 = LayerMetal(
            name="M2",
            gds_layer_number=2,
            direction="h",
            min_length=2160, min_end_to_end=1080,
            offset=0, width=[400], space=[500], stop_pitch=1080, stop_point=540, stop_offset=0,
        )
        m3 = LayerMetal(
            name="M3",
            gds_layer_number=3,
            direction="v",
            min_length=1500, min_end_to_end=1000,
            offset=0, width=[600], space=[480], stop_pitch=900, stop_point=200, stop_offset=0
        )
        m4 = LayerMetal(
            name="M4",
            gds_layer_number=4,
            direction="h",
            min_length=2160, min_end_to_end=1080,
            offset=0, width=[400], space=[500], stop_pitch=1080, stop_point=540, stop_offset=0,
        )
        m5 = LayerMetal(
            name="M5",
            gds_layer_number=5,
            direction="v",
            min_length=1500, min_end_to_end=1000,
            offset=0, width=[600], space=[480], stop_pitch=900, stop_point=200, stop_offset=0
        )
        m6 = LayerMetal(
            name="M6",
            gds_layer_number=6,
            direction="h",
            min_length=2160, min_end_to_end=1080,
            offset=0, width=[400], space=[500], stop_pitch=1080, stop_point=540, stop_offset=0,
        )
        v1 = LayerViaSet(name="V1", gds_layer_number=21, default_via=LayerVia(
            name="V1",
            gds_layer_number=21,
            stack=('M1', 'M2'),
            width_x=600, width_y=400, space_x=600, space_y=300,
        ))
        v2 = LayerViaSet(name="V2", gds_layer_number=22, default_via=LayerVia(
            name="V2",
            gds_layer_number=22,
            stack=('M2', 'M3'),
            width_x=600, width_y=400, space_x=300, space_y=600,
        ))
        v3 = LayerViaSet(name="V3", gds_layer_number=23, default_via=LayerVia(
            name="V3",
            gds_layer_number=23,
            stack=('M3', 'M4'),
            width_x=600, width_y=400, space_x=600, space_y=300,
        ))
        v4 = LayerViaSet(name="V4", gds_layer_number=24, default_via=LayerVia(
            name="V4",
            gds_layer_number=24,
            stack=('M4', 'M5'),
            width_x=600, width_y=400, space_x=300, space_y=600,
        ))
        v5 = LayerViaSet(name="V5", gds_layer_number=25, default_via=LayerVia(
            name="V5",
            gds_layer_number=24,
            stack=('M5', 'M6'),
            width_x=600, width_y=400, space_x=600, space_y=300,
        ))

        self.pdk_v2 = PDK(name=
                       """Mock FinFET technology with non-uniform metal grids. \
                       This file is auto-generated using tests/schema/test_pdk.py""",
                       layers={'M1': m1, 'M2': m2, 'M3': m3, 'M4': m4, 'M5': m5, 'M6': m6,
                               'V1': v1, 'V2': v2, 'V3': v3, 'V4': v4, 'V5': v5})

        my_dir = pathlib.Path(__file__).resolve().parent
        with open(my_dir / "layers_cand.json", "wt") as fp:
            fp.write(json.dumps(self.pdk_v2.dict(), indent=2) + '\n')
