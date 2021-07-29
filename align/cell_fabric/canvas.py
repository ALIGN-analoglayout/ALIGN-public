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

    def addWire( self, wire, netName, c, bIdx, eIdx, *, bS=None, eS=None, netType="drawing"):
        self.transform_and_add( wire.segment( netName, c, bIdx, eIdx, bS=bS, eS=eS, netType=netType))

    def addRegion( self, region, netName, grid_x0, grid_y0, grid_x1, grid_y1):
        self.transform_and_add( region.segment( netName, grid_x0, grid_y0, grid_x1, grid_y1, netType="drawing"))

    def addVia( self, via, netName, cx, cy):
        self.transform_and_add( via.segment( netName, cx, cy, netType="drawing"))

    def addWireAndViaSet( self, netName, wire, via, c, listOfIndices, *, bIdx=None, eIdx=None, netType="drawing"):
        """March through listOfIdx, compute physical coords (including via extensions), keep bounding box, draw wire."""
        self.addWireAndMultiViaSet( netName, wire, c, [ (via, listOfIndices)], bIdx=bIdx, eIdx=eIdx, netType=netType)

    def addWireAndMultiViaSet( self, netName, wire, c, listOfPairs, *, bIdx=None, eIdx=None, netType="drawing"):
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
                    self.addVia( via, netName, c, q)
                else:
                    self.addVia( via, netName, q, c)

        self.addWire( wire, netName, c, mn, mx, netType=netType)

    def join_wires(self, wire, exclude_nets=None, include_nets=None, max_length=None):
        """
        Merge neighbor wires on the same center line if wire widths match and merged wire length < MaxL
        :param wire: wire generator
        :param exclude_nets: set of nets to be excluded (precedes include_nets)
        :param include_nets: set of nets to be included (if None, merge any wire)
        :param max_length: maximum length of joined wire segments (must be less than
        :return:
        """

        if exclude_nets is None:
            exclude_nets = set()
        else:
            exclude_nets = set(exclude_nets)

        if include_nets is not None:
            include_nets = set(include_nets)

        assert max_length is None or max_length > 0
        max_l = self.pdk[wire.layer]['MaxL']
        if max_l is None:
            max_l = float('inf')
        if max_length is not None and max_length < max_l:
            max_l = max_length

        self.terminals = self.removeDuplicates(allow_opens=True).copy()
        m_lines = self.rd.store_scan_lines[wire.layer]
        iy = 1 if wire.direction.upper() == 'V' else 0
        ix = 0 if wire.direction.upper() == 'V' else 1
        for (cl, sl) in m_lines.items():
            new_length = 0
            c_idx = wire.clg.inverseBounds(cl//2)[0]
            for (idx, slr) in enumerate(sl.rects):
                if slr.netName is None or slr.netName in exclude_nets:
                    new_length = 0
                    continue
                if include_nets is not None and slr.netName not in include_nets:
                    new_length = 0
                    continue
                # Connect with successor
                if idx+1 < len(sl.rects):
                    next_slr = sl.rects[idx+1]
                    next_w = next_slr.rect[ix + 2] - next_slr.rect[ix]
                    w = slr.rect[ix + 2] - slr.rect[ix]
                    new_length += next_slr.rect[iy+2] - slr.rect[iy]
                    if slr.netName == next_slr.netName and w == next_w and new_length <= max_l:
                        (b_idx, _) = wire.spg.inverseBounds(slr.rect[iy])
                        (_, e_idx) = wire.spg.inverseBounds(next_slr.rect[iy+2])
                        self.addWire(wire, slr.netName, None, c_idx, b_idx, e_idx)
                        new_length -= next_slr.rect[iy+2] - next_slr.rect[iy]
                    else:
                        new_length = 0
        self.terminals = self.removeDuplicates(allow_opens=True).copy()

    def drop_via(self, via, exclude_nets=None, include_nets=None):

        if exclude_nets is None:
            exclude_nets = set()
        else:
            exclude_nets = set(exclude_nets)

        if include_nets is not None:
            include_nets = set(include_nets)

        self.terminals = self.removeDuplicates(allow_opens=True).copy()

        [mb, ma] = self.pdk[via.layer]['Stack']
        assert mb is not None, f'Lower layer is not a metal'
        assert ma is not None, f'Upper layer is not a metal'

        # mh: horizontal wire, mv: vertical wire
        if self.pdk[mb]['Direction'].upper() == 'H':
            mh = self._find_generator(mb)
            mv = self._find_generator(ma)
        else:
            mh = self._find_generator(ma)
            mv = self._find_generator(mb)
        mh_lines = self.rd.store_scan_lines[mh.layer]
        mv_lines = self.rd.store_scan_lines[mv.layer]

        via_matrix = self._construct_via_matrix(via)

        for (mh_cl, mh_sl) in mh_lines.items():
            for (_, mh_slr) in enumerate(mh_sl.rects):
                mh_name = mh_slr.netName
                if mh_name is None or mh_name in exclude_nets:
                    continue
                if include_nets is not None and mh_name not in include_nets:
                    continue
                for (mv_cl, mv_sl) in mv_lines.items():
                    # Check only the scan lines that can intersect with ml_slr
                    if mv_cl < 2*mh_slr.rect[0]:
                        continue
                    if mv_cl > 2*mh_slr.rect[2]:
                        continue  # Scanlines are not in order
                    for (_, mv_slr) in enumerate(mv_sl.rects):
                        mv_name = mv_slr.netName
                        if mv_name is None or mv_name != mh_name:
                            continue
                        # Check only the rectangles that overlap with the centerline
                        if mh_cl > 2*mv_slr.rect[3]:
                            continue
                        if mh_cl < 2*mv_slr.rect[1]:
                            break
                        # Check if via exists
                        if mh_cl in via_matrix and mv_cl in via_matrix[mh_cl]:
                            continue
                        # Check if DR-clean via can dropped
                        self._drop_via_if_dr_clean(via, via_matrix, mh, mh_cl, mh_slr, mv, mv_cl, mv_slr)

    def _find_generator(self, layer):
        for key, gen in self.generators.items():
            if gen.layer == layer:
                return gen
        assert False, f'A generator not found for {layer}'

    def _construct_via_matrix(self, via):
        via_lines = self.rd.store_scan_lines[via.layer]
        via_matrix = dict()
        for (_, via_sl) in via_lines.items():
            for (_, via_slr) in enumerate(via_sl.rects):
                mh_cl = via_slr.rect[0] + via_slr.rect[2]
                mv_cl = via_slr.rect[1] + via_slr.rect[3]
                if mh_cl not in via_matrix:
                    via_matrix[mh_cl] = dict()
                via_matrix[mh_cl][mv_cl] = via_slr.rect.copy()
        return via_matrix

    def _drop_via_if_dr_clean(self, via, via_matrix, mh, mh_cl, mh_slr, mv, mv_cl, mv_slr):
        via_def = self.pdk[via.layer]
        via_half_w = via_def["WidthX"] // 2
        via_half_h = via_def["WidthY"] // 2
        via_rect = [mv_cl//2 - via_half_w, mh_cl//2 - via_half_h,
                    mv_cl//2 + via_half_w, mh_cl//2 + via_half_h]

        [mb, _] = self.pdk[via.layer]['Stack']
        if mh.layer == mb:
            venca_h = via_def["VencA_L"]
            venca_v = via_def["VencA_H"]
        else:
            venca_h = via_def["VencA_H"]
            venca_v = via_def["VencA_L"]

        # Check via enclosure along the way (perpendicular should be correct by grid definition)
        if mh_slr.rect[0] > via_rect[0] - venca_h:
            return
        if mh_slr.rect[2] < via_rect[2] + venca_h:
            return
        if mv_slr.rect[1] > via_rect[1] - venca_v:
            return
        if mv_slr.rect[3] < via_rect[3] + venca_v:
            return

        # check left and right neighbors
        if mh_cl in via_matrix:
            for v_cl, r in via_matrix[mh_cl].items():
                if (r[2] < via_rect[0]) and (r[2] > via_rect[0]-via_def["SpaceX"]):
                    return
                if (r[0] > via_rect[2]) and (r[0] < via_rect[2]+via_def["SpaceX"]):
                    return

        (b_idx, _) = mh.clg.inverseBounds(mh_cl//2 - 1)
        mh_cl_m1 = 2*mh.clg.value(b_idx)[0]
        (_, b_idx) = mh.clg.inverseBounds(mh_cl//2 + 1)
        mh_cl_p1 = 2*mh.clg.value(b_idx)[0]

        # check via below
        if mh_cl_m1 in via_matrix:
            for v_cl, r in via_matrix[mh_cl_m1].items():
                if v_cl == mv_cl:
                    if (r[3] < via_rect[1]) and (r[3] > via_rect[1]-via_def["SpaceY"]):
                        return

        # check via above
        if mh_cl_p1 in via_matrix:
            for v_cl, r in via_matrix[mh_cl_p1].items():
                if v_cl == mv_cl:
                    if (r[1] > via_rect[3]) and (r[1] < via_rect[3]+via_def["SpaceY"]):
                        return

        self.addVia(via, mh_slr.netName, None,
                    mv.clg.inverseBounds(mv_cl // 2)[0],
                    mh.clg.inverseBounds(mh_cl//2)[0])

        if mh_cl not in via_matrix:
            via_matrix[mh_cl] = dict()
        via_matrix[mh_cl][mv_cl] = via_rect.copy()

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
                        # assert nm is not None
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
                        # assert nm is not None
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

    def removeDuplicates( self, *, nets_allowed_to_be_open=None, allow_opens=False, silence_errors=False):
        self.rd = RemoveDuplicates( self, nets_allowed_to_be_open=nets_allowed_to_be_open, allow_opens=allow_opens)
        return self.rd.remove_duplicates(silence_errors=silence_errors)

    def gen_data( self, *, draw_grid=False, run_drc=True, run_pex=True, nets_allowed_to_be_open=None, postprocess=False):

        self.computeBbox()

        data = { 'bbox' : self.bbox.toList(),
                 'globalRoutes' : [],
                 'globalRouteGrid' : [],
                 'terminals' : self.removeDuplicates(nets_allowed_to_be_open=nets_allowed_to_be_open)}

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

        if postprocess:
            data['terminals'] = self.postprocessor.run(data['terminals'])

        return data

    def writeJSON(self, fp, *, draw_grid=False, run_drc=True, run_pex=True, postprocess=False):
        data = self.gen_data( draw_grid=draw_grid, run_drc=run_drc, run_pex=run_pex, postprocess=postprocess)
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
