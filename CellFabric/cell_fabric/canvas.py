import copy
import collections
import json

from . import transformation
from .remove_duplicates import RemoveDuplicates
from .utilities import DesignRuleCheck, ParasiticExtraction
from .pdk import Pdk
from .generators import *
from .grid import *

from .gen_gds_json import translate

from . import routing_collateral

import datetime

import io
import gdsconv.json2gds

class Canvas:
    def computeBbox( self):
        """Set the bbox based on the extend of the included rectangles. You might not want to do this, instead setting it explicitly"""
        self.bbox = transformation.Rect(None,None,None,None)
        for term in self.terminals:
            r = transformation.Rect( *term['rect'])
            if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
            if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
            if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
            if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury

    def addGen( self, gen):
        assert gen.nm not in self.generators, gen.nm
        self.generators[gen.nm] = gen
        return gen
 
    def transform_and_add( self, s):
        r = transformation.Rect( *s['rect'])
        s['rect'] = self.trStack[-1].hitRect(r).canonical().toList()
        self.terminals.append( s)

    def addWire( self, wire, netName, pinName, c, bIdx, eIdx, *, bS=None, eS=None):
        self.transform_and_add( wire.segment( netName, pinName, c, bIdx, eIdx, bS=bS, eS=eS))
       
    def addRegion( self, region, netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1):
        self.transform_and_add( region.segment( netName, pinName, grid_x0, grid_y0, grid_x1, grid_y1))

    def addVia( self, via, netName, pinName, cx, cy):
        self.transform_and_add( via.segment( netName, pinName, cx, cy))

    def addWireAndViaSet( self, netName, pinName, wire, via, c, listOfIndices, *, bIdx=None, eIdx=None):
        """March through listOfIdx, compute physical coords (including via extensions), keep bounding box, draw wire."""
        self.addWireAndMultiViaSet( netName, pinName, wire, c, [ (via, listOfIndices)], bIdx=bIdx, eIdx=eIdx)

    def addWireAndMultiViaSet( self, netName, pinName, wire, c, listOfPairs, *, bIdx=None, eIdx=None):
        """March through listOfPairs (via, idx), compute physical coords (including via extensions), keep bounding box, draw wire."""

        tuples = [(via.v_clg if wire.direction == 'h' else via.h_clg).value(idx, check=False)[0] for (via,listOfIndices) in listOfPairs for idx in listOfIndices]

#
# Find min and max indices (using physical coordinate as key)
#
        mnP = min(tuples)
        mxP = max(tuples)

# should be the real enclosure but this finds the next grid point
        enclosure = 1
        (mn, _) = wire.spg.inverseBounds( mnP-enclosure)
        (_, mx) = wire.spg.inverseBounds( mxP+enclosure)

        for (via,listOfIndices) in listOfPairs:
            for q in listOfIndices:
                if wire.direction == 'v':
                    self.addVia( via, netName, None, c, q)
                else:
                    self.addVia( via, netName, None, q, c)

        self.addWire( wire, netName, pinName, c, mn, mx)

    def asciiStickDiagram( self, v1, m2, v2, m3, matrix, *, xpitch=4, ypitch=2):
        # clean up text input
        a = matrix.split( '\n')[1:-1]

        ncols = max([ len(row) for row in a])
        assert (ncols-1) % xpitch == 0
        nrows = len(a)
        assert (nrows-1) % ypitch == 0

        paddedA = []
        for row in a:
            paddedA.append( row + ' '*(ncols-len(row)))
        assert max([ len(row) for row in paddedA]) == ncols

        for x in range(ncols):
            for y in range(nrows):
                if x % xpitch != 0 and y % ypitch != 0:
                    assert paddedA[y][x] == ' '

        # find all metal2
        for y in reversed(range( (nrows-1) // ypitch + 1)):
            row = paddedA[nrows-1-y*ypitch] + ' '
            started = False
            nm = None
            via1s = []
            via2s = []

            for (x,c) in enumerate( row):
                if c == ' ':
                    if started:
                        # close off wire
#                        assert nm is not None
                        self.addWireAndMultiViaSet( nm, None, m2, y, [ (v1, via1s), (v2, via2s)]) 
                        started = False
                        nm = None
                        via1s = []
                        via2s = []
                elif c in ['+','*']:
                    assert x % xpitch == 0
                    via1s.append( x//xpitch)
                    started = True
                elif c in ['/','*']:
                    assert x % xpitch == 0
                    via2s.append( x//xpitch)
                    started = True
                elif c in ['=','═','╬']:
                    assert started
                elif c in ['|','║']:
                    pass
                else:
                    if started:
                        if nm is None:
                            nm = c
                        else:
                            nm = nm + c

        # find all metal3
        for x in range( (ncols-1) // xpitch + 1):
            col = ''.join([ paddedA[nrows-1-y][x*xpitch] for y in range(nrows)]) + ' '
            started = False
            nm = None
            via2s = []

            for (y,c) in enumerate( col):
                if c == ' ':
                    if started:
                        # close off wire
#                        assert nm is not None
                        self.addWireAndMultiViaSet( nm, None, m3, x, [ (v2, via2s)]) 
                        started = False
                        nm = None
                        via1s = []
                        via2s = []
                elif c in ['/','*']:
                    assert y % ypitch == 0
                    via2s.append( y//ypitch)
                    started = True
                elif c in ['|','║','╬']:
                    assert started
                elif c in ['=','═','+']:
                    pass
                else: # walking bottom-to-top (increasing y coord) so construct the name in reverse
                    if started:
                        if nm is None:
                            nm = c
                        else:
                            nm = c + nm

    def __init__( self, pdk=None):
        self.pdk = pdk
        self.terminals = []
        self.generators = collections.OrderedDict()
        self.trStack = [transformation.Transformation()]
        self.rd = None
        self.drc = None
        self.layer_stack = [( "via1", ("M1", "M2")), 
                            ( "via2", ("M3", "M2"))]

    def pushTr( self, tr):
        self.trStack.append( self.trStack[-1].postMult( tr))

    def hitTopTr( self, tr):
        self.trStack[-1] = self.trStack[-1].postMult( tr)

    def popTr( self):
        self.trStack.pop()
        assert self.trStack != []

    def removeDuplicates( self):
        self.rd = RemoveDuplicates( self)
        return self.rd.remove_duplicates()

    def gen_data( self):
        self.computeBbox()

        data = { 'bbox' : self.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : self.removeDuplicates()}

        if self.pdk is not None:
            self.drc = DesignRuleCheck( self)
            self.drc.run()

        return data

    def writeJSON(self, fp):
        data = self.gen_data()
        json.dump( data, fp, indent=2)
        return data

    def writeGDS(self, fp1, timestamp=None):

        with io.StringIO() as fp0:
            self.writeJSON(fp0)
            contents = fp0.getvalue()

        with io.StringIO( contents) as fp0, \
             io.StringIO() as fp_tmp:
            translate( 'foo', '', fp0, fp_tmp, timestamp=timestamp)
            contents2 = fp_tmp.getvalue()

        with io.StringIO( contents2) as fp0:
            gdsconv.json2gds.convert_GDSjson_GDS_fps( fp0, fp1)

    def loadPDK(self, filename):
        assert self.pdk is None, "PDK already loaded. Cannot re-load"
        self.pdk = Pdk().load( filename)

    def checkDesignRules(self):
        assert self.pdk is not None, "loadPDK() must be run before checkDesignRules()"
        assert self.rd is not None, "removeDuplicates() must be run before checkDesignRules()"
        errors = DesignRuleCheck( self).run()
        assert errors == 0, f"Found {errors} DRC Errors! Exiting"

    def extractParasitics(self):
        assert self.pdk is not None, "loadPDK() must be run before extractParasitics()"
        assert self.rd is not None, "removeDuplicates() must be run before extractParasitics()"
        return ParasiticExtraction( self).run()


    def generate_routing_collateral(self, dirname):
        return routing_collateral.gen( self, dirname)



class DefaultCanvas(Canvas):

    def __init__( self, pdk):
        super().__init__(pdk)
        assert self.pdk is not None, "Cannot initialize DefaultCanvas without a pdk"
        self.layer_stack = pdk.get_electrical_connectivity()
        for layer, info in self.pdk.items():
            if layer.startswith('M'):
                self._create_metal(layer, info)
            elif layer.startswith('V'):
                self._create_via(layer, info)

    def _get_spg_pitch( self, layer):
        return min(self.pdk[layer]['Pitch']) if isinstance(self.pdk[layer]['Pitch'], list) else self.pdk[layer]['Pitch']

    def _get_spg_stop( self, metal, viaenc):
        w = min(self.pdk[metal]['Width']) if isinstance(self.pdk[metal]['Width'], list) else self.pdk[metal]['Width']
        return w // 2 + viaenc

    def _create_metal( self, layer, info):
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
                spg_pitch, spg_stop = self._get_spg_pitch(pm), self._get_spg_stop(pm, self.pdk[pv]['VencA_H'])
            elif pm is None:
                spg_pitch, spg_stop = self._get_spg_pitch(nm), self._get_spg_stop(nm, self.pdk[nv]['VencA_L'])
            else:
                pm_pitch, nm_pitch = self._get_spg_pitch(pm), self._get_spg_pitch(nm)
                if pm_pitch <= nm_pitch:
                    spg_pitch, spg_stop = pm_pitch, self._get_spg_stop(pm, self.pdk[pv]['VencA_H'])
                else:
                    spg_pitch, spg_stop = nm_pitch, self._get_spg_stop(nm, self.pdk[nv]['VencA_L'])
            layer = layer.lower()
            if len(info['Color']) == 0:
                clg = UncoloredCenterLineGrid( pitch=info['Pitch'], width=info['Width'], offset=info['Pitch']//2)
            else:
                clg = ColoredCenterLineGrid( colors=info['Color'], pitch=info['Pitch'], width=info['Width'], offset=info['Pitch']//2)
            setattr(self, layer, self.addGen(
                Wire(layer, base_layer, info['Direction'], clg = clg,
                     spg = EnclosureGrid( pitch=spg_pitch, offset=spg_pitch//2, stoppoint=spg_stop, check=True))
            ))

    def _create_via( self, layer, info):
        if self.pdk[info['Stack'][0]]['Direction'] == 'h':
            assert self.pdk[info['Stack'][1]]['Direction'] == 'v', f"{info['Stack']} both appear to be horizontal"
            h_clg = getattr(self, info['Stack'][0].lower()).clg
            v_clg = getattr(self, info['Stack'][1].lower()).clg
        else:
            assert self.pdk[info['Stack'][1]]['Direction'] == 'h', f"{info['Stack']} both appear to be vertical"
            v_clg = getattr(self, info['Stack'][0].lower()).clg
            h_clg = getattr(self, info['Stack'][1].lower()).clg
        setattr(self, layer.lower(), self.addGen(
            # TODO: layer.replace('V', 'via') is a temporary hack to reuse common tests. 
            #       Fix tests & replace with layer
            Via(layer.lower(), layer.replace('V', 'via'), h_clg = h_clg, v_clg = v_clg)
        ))

    def _find_adjoining_layers( self, layer):
        pm = pv = nv = nm = None
        for (v, (m0, m1)) in self.layer_stack:
            if layer == m0:
                nv = v
                nm = m1
            elif layer == m1:
                pv = v
                pm = m0
        assert nm is not None or pm is not None, f"Could not trace any connections for {layer}"
        return (pm, pv, nv, nm)
