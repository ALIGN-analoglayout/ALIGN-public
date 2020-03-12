import collections
import json
import io

from . import transformation
from .remove_duplicates import RemoveDuplicates
from .drc import DesignRuleCheck
from .pex import ParasiticExtraction
from .postprocess import PostProcessor
from .pdk import Pdk
from .generators import *
from .grid import *
from .gen_gds_json import translate
from . import routing_collateral
from ..gdsconv import json2gds

LayoutDevice = collections.namedtuple('LayoutDevice', ['parameters', 'pins'])

class Canvas:
    def computeBbox( self):
        """Set the bbox based on the extend of the included rectangles. You might not want to do this, instead setting it explicitly"""
        if self.bbox is None:
            self.bbox = transformation.Rect(None,None,None,None)
            for term in self.terminals:
                r = transformation.Rect( *term['rect'])
                if self.bbox.llx is None or self.bbox.llx > r.llx: self.bbox.llx = r.llx
                if self.bbox.lly is None or self.bbox.lly > r.lly: self.bbox.lly = r.lly
                if self.bbox.urx is None or self.bbox.urx < r.urx: self.bbox.urx = r.urx
                if self.bbox.ury is None or self.bbox.ury < r.ury: self.bbox.ury = r.ury

    def setBboxFromBoundary( self):
        res = []
        for term in self.terminals:
            if term['layer'] == 'Boundary':
                res.append(term)
        assert len(res) == 1
        self.bbox = transformation.Rect( *res[0]['rect'])

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

        # Get minimum & maximum via centerpoints (in terms of physical coords)
        dim_tuples = [(via.v_clg if wire.direction == 'h' else via.h_clg).value(idx, check=False)[0] for (via,listOfIndices) in listOfPairs for idx in listOfIndices]
        mnP = min(dim_tuples)
        mxP = max(dim_tuples)

        # Adjust for via enclosure & obtain min & max wire coordinates
        via_list = [via for (via,listOfIndices) in listOfPairs for idx in listOfIndices]
        mnP -= via_list[dim_tuples.index(mnP)].center_to_metal_edge(wire.direction)
        mxP += via_list[dim_tuples.index(mxP)].center_to_metal_edge(wire.direction)

        # Compute abstract grid coordinates
        (mn, _) = wire.spg.inverseBounds( mnP )
        (_, mx) = wire.spg.inverseBounds( mxP )

        # Snap to legal coordinates
        mn = wire.spg.snapToLegal(mn, -1)
        mx = wire.spg.snapToLegal(mx, 1)

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

    def _initialize_layer_stack(self):
        """layer_stack expects tuple of the form ( via, (metal_vertical, metal_horizontal))"""
        self.layer_stack = [(l, (pl, nl)) if self.pdk[nl]['Direction'] == 'h' else (l, (nl, pl)) \
            for l, (pl, nl) in self.pdk.get_via_stack() if l.startswith('V')]

    def __init__( self, pdk=None, gds_layer_map=None):
        self.pdk = pdk
        self.subinsts = collections.defaultdict(
            lambda: LayoutDevice(
                collections.defaultdict(None),
                collections.defaultdict(set)))
        self.terminals = []
        self.postprocessor = PostProcessor()
        self.generators = collections.OrderedDict()
        self.trStack = [transformation.Transformation()]
        self.rd = None
        self.drc = None
        self.layer_stack = [( "via1", ("M1", "M2")),
                            ( "via2", ("M3", "M2"))]
        self.gds_layer_map = gds_layer_map
        self.bbox = None
        if self.pdk is not None:
            self._initialize_layer_stack()

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

    def gen_data( self, *, draw_grid=False, run_drc=True, run_pex=True):

        self.computeBbox()
        self.postprocessor.run(self.terminals)

        data = { 'bbox' : self.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : self.removeDuplicates()}

        if len(self.subinsts) > 0:
            data['subinsts'] = {inst: v.parameters for inst, v in self.subinsts.items()}

        if self.pdk is not None:
            if draw_grid:
                self.draw_grid(data)

            if run_drc:
                self.drc = DesignRuleCheck( self)
                self.drc.run()
            if run_pex:
                self.pex = ParasiticExtraction( self)
                self.pex.run()

        return data

    def writeJSON(self, fp, *, draw_grid=False):
        data = self.gen_data( draw_grid=draw_grid)
        json.dump( data, fp, indent=2)
        return data

    def draw_grid(self,data):
        width = self.bbox.urx
        height = self.bbox.ury

        ly = "M1"
        if ly in self.pdk:
            pitch = self.pdk[ly]["Pitch"]
            assert self.pdk[ly]["Direction"] == 'v'
            assert pitch == 80

            for ix in range( (width+pitch-1)//pitch):
                x = pitch*ix
                r = [ x-1, 0, x+1, height]
                data['terminals'].append( { "netName": ly + '_grid', "layer": ly, "rect": r})


        ly = "M2"
        if ly in self.pdk:
            pitch = self.pdk[ly]["Pitch"]
            assert pitch == 84
            assert self.pdk[ly]["Direction"] == 'h'

            for iy in range( (height+pitch-1)//pitch):
                y = pitch*iy
                r = [ 0, y-1, width, y+1]
                data['terminals'].append( { "netName": ly + '_grid', "layer": ly, "rect": r})


    def writeGDS(self, fp1, timestamp=None):

        assert self.gds_layer_map is not None

        with io.StringIO() as fp0:
            self.writeJSON(fp0)
            contents = fp0.getvalue()

        with io.StringIO( contents) as fp0, \
             io.StringIO() as fp_tmp:
            # TODO: Update this
            raise NotImplementedError("Translate api has changed but canvas hasn't been updated")
            translate( 'foo', '', fp0, fp_tmp, self.gds_layer_map, timestamp=timestamp)
            contents2 = fp_tmp.getvalue()

        with io.StringIO( contents2) as fp0:
            json2gds.convert_GDSjson_GDS_fps( fp0, fp1)

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
