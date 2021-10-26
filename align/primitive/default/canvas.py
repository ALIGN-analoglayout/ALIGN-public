import math
import functools

from ..main import get_generator

from ...cell_fabric.canvas import Canvas
from ...cell_fabric.generators import *
from ...cell_fabric.grid import *
from .via import ColorClosure

import logging
logger = logging.getLogger(__name__)

class DefaultCanvas(Canvas):

    def __init__( self, pdk, *, check=True):
        super().__init__(pdk)
        self._create_metal_canvas( check=check)
        self.boundary = self.addGen( Region( 'boundary', 'Boundary', h_grid=self.m2.clg, v_grid=self.m1.clg))

    #
    # Automatically Create Metal Generators from layers.json
    #

    def _create_metal_canvas(self, *, check=True):
        self.gds_layer_map = self.pdk.get_gds_map()
        for layer, info in self.pdk.items():
            if layer.startswith('M'):
                self._create_metal(layer, info, check=check)
            elif layer.startswith('V'):
                self._create_via(layer, info)

    def _get_metal_width( self, layer):
        return self.pdk[layer]['Width'][0] if isinstance(self.pdk[layer]['Width'], list) else self.pdk[layer]['Width']

    def _get_metal_pitch( self, layer):
        return self.pdk[layer]['Pitch'][0] if isinstance(self.pdk[layer]['Pitch'], list) else self.pdk[layer]['Pitch']

    def _get_metal_offset( self, layer):
        return self.pdk[layer]['Offset'][0] if isinstance(self.pdk[layer]['Offset'], list) else self.pdk[layer]['Offset']

    def _get_via_ext( self, metal, via):
        viaenc = self.pdk[via][f'VencA_L'] if self.pdk[via]['Stack'][0] == metal else self.pdk[via][f'VencA_H']
        viawidth = self.pdk[via]['WidthX'] if self.pdk[metal]['Direction'] == 'h' else self.pdk[via]['WidthY']
        return viawidth // 2 + viaenc

    def _create_metal( self, layer, info, *, check=True):
        if 'Color' in info and len(info['Color']) > 0:
            logger.debug( f"Registering ColorClosure for layer {layer}")
            self.postprocessor.register(layer, ColorClosure( info=info, errors=self.postprocessor.errors))

        if isinstance(info['Width'], list):
            # TODO: Figure out what multiple metal widths even means. Just doing first width for now
            # for i in range(0, len(info['Width'])):
            for i in range(0, 1):
                self._create_metal(layer, \
                    {k: v[i] if k in ['Pitch', 'Width', 'MinL', 'MaxL'] else v for k, v in info.items()})
        else:
            base_layer = layer.split('_')[0]
            (pm, pv, nv, nm) = self._find_adjoining_layers(base_layer)
            if nm is None:
                logger.debug(f'spg for {base_layer} aligned to {pm}')
                spg_pitch, spg_stop, spg_offset = (self._get_metal_pitch(pm),
                                                   self._get_via_ext(base_layer, pv),
                                                   self._get_metal_offset(pm))
            elif pm is None:
                logger.debug(f'spg for {base_layer} aligned to {nm}')
                spg_pitch, spg_stop, spg_offset = (self._get_metal_pitch(nm),
                                                   self._get_via_ext(base_layer, nv),
                                                   self._get_metal_offset(nm))
            else:
                pm_pitch, nm_pitch = self._get_metal_pitch(pm), self._get_metal_pitch(nm)
                if pm_pitch <= nm_pitch:
                    logger.debug(f'spg for {base_layer} aligned to {pm}')
                    spg_pitch, spg_stop, spg_offset = (pm_pitch,
                                                       self._get_via_ext(base_layer, pv),
                                                       self._get_metal_offset(pm))
                else:
                    logger.debug(f'spg for {base_layer} aligned to {nm}')
                    spg_pitch, spg_stop, spg_offset = (nm_pitch,
                                                       self._get_via_ext(base_layer, nv),
                                                       self._get_metal_offset(nm))

                ## TODO: Stoppoint shall satisfy both upper and lower layers
                # spg_stop = max(self._get_via_ext(base_layer, nv), self._get_via_ext(base_layer, pv)) 

            logger.debug(f"Enclosure grid for {layer}, pitch={spg_pitch}, offset={spg_offset}, stop={spg_stop}")

            layer = layer.lower()
            if len(info['Color']) == 0:
                clg = UncoloredCenterLineGrid(pitch=self._get_metal_pitch(base_layer),
                                              width=self._get_metal_width(base_layer),
                                              offset=self._get_metal_offset(base_layer))
            else:
                clg = ColoredCenterLineGrid(colors=info['Color'],
                                            pitch=self._get_metal_pitch(base_layer),
                                            width=self._get_metal_width(base_layer),
                                            offset=self._get_metal_offset(base_layer))

            setattr(self, layer, self.addGen(
                Wire(layer, base_layer, info['Direction'], clg = clg,
                     spg = EnclosureGrid( pitch=spg_pitch, offset=spg_offset, stoppoint=spg_stop, check=check))
            ))

    def _create_via( self, layer, info):
        if any(x is None for x in info['Stack']):
            logger.debug(f"Cannot create {layer} via automatically. One or more metal layers are None.")
            return

        if self.pdk[info['Stack'][0]]['Direction'] == 'h':
            assert self.pdk[info['Stack'][1]]['Direction'] == 'v', f"{info['Stack']} both appear to be horizontal"
            h_clg = getattr(self, info['Stack'][0].lower()).clg
            v_clg = getattr(self, info['Stack'][1].lower()).clg
            h_ext = self._get_via_ext(info['Stack'][0], layer)
            v_ext = self._get_via_ext(info['Stack'][1], layer)
        else:
            assert self.pdk[info['Stack'][1]]['Direction'] == 'h', f"{info['Stack']} both appear to be vertical"
            v_clg = getattr(self, info['Stack'][0].lower()).clg
            h_clg = getattr(self, info['Stack'][1].lower()).clg
            v_ext = self._get_via_ext(info['Stack'][0], layer)
            h_ext = self._get_via_ext(info['Stack'][1], layer)
        setattr(self, layer.lower(), self.addGen(
            Via(layer.lower(), layer,
                h_clg=h_clg, v_clg=v_clg,
                WidthX=info['WidthX'], WidthY=info['WidthY'],
                h_ext=h_ext, v_ext=v_ext)
        ))

        if 'ViaCut' in info:
            self.postprocessor.register(layer, functools.partial(
                get_generator(info['ViaCut']['Gen'], self.pdk.layerfile.parent),
                **{k: v for k, v in info['ViaCut'].items() if k != 'Gen'}))



    def _find_adjoining_layers( self, layer):
        pm = pv = nv = nm = None
        for (v, (m0, m1)) in self.pdk.get_via_stack():
            if layer == m0:
                nv = v
                nm = m1
            elif layer == m1:
                pv = v
                pm = m0
        assert nm is not None or pm is not None, f"Could not trace any connections for {layer}"
        return (pm, pv, nv, nm)
