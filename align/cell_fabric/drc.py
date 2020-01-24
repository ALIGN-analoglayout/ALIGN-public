import pprint
import logging
logger = logging.getLogger(__name__)

class DesignRuleCheck():
    def __init__(self, canvas):
        self.canvas = canvas
        self.errors = []

    @property
    def num_errors(self):
        return len(self.errors)

    def run(self):
        '''
        Run DRC on self.canvas & report errors if any

        Note: self.canvas must already contain 'rd'
              (aka removeDuplicates has been run)
        '''

        for (layer, vv) in self.canvas.rd.store_scan_lines.items():
            if not (layer.startswith('V') or layer.startswith('M')) or layer not in self.canvas.pdk:
                continue
            if self.canvas.rd.layers[layer] == '*':
                self._check_via_rules(layer, vv)
                self._check_via_enclosure_rules(layer, vv)
            else:
                self._check_metal_rules(layer, vv)
        for error in self.errors:
            logger.warning(pprint.pformat(error))
        return self.num_errors

    def _check_via_rules(self, layer, vv):
        '''TODO : Add via pattern checking rules '''
        space = self.canvas.pdk[layer]['SpaceX']
        return space

    def _check_via_enclosure_rules(self, layer, vv):
        '''Check via enclosures.'''
        v = self.canvas.pdk[layer]
        [ly_l,ly_u] = v['Stack']
        if ly_l is not None:
            ml_dir = self.canvas.pdk[ly_l]['Direction'].upper()
            assert ml_dir in ['V','H']
        if ly_u is not None:
            mu_dir = self.canvas.pdk[ly_u]['Direction'].upper()
            assert mu_dir in ['V','H']

        def check_single_metal( r, ly, metal_dir, enclosure_value):
            o = 1 if metal_dir == 'V' else 0
            metal_r = self._find_rect_covering_via( r, ly, metal_dir)
            if metal_r[o+0] > r.rect[o+0] - enclosure_value or metal_r[o+2] < r.rect[o+2] + enclosure_value:
                self.errors.append( f"ENCLOSURE: {ly} {metal_r} does not sufficiently surround {layer} {r.rect}, {enclosure_value}")

        for _, sl in vv.items():
            for r in sl.rects:
                if ly_l is not None: check_single_metal( r, ly_l, ml_dir, v['VencA_L'])
                if ly_u is not None: check_single_metal( r, ly_u, mu_dir, v['VencA_H'])

    def _find_rect_covering_via( self, r, ly, metal_dir):
        cx2 = r.rect[0]+r.rect[2]
        cy2 = r.rect[1]+r.rect[3]
        c2a,c2p,o = (cx2,cy2,1) if metal_dir == 'V' else (cy2,cx2,0)
        sl = self.canvas.rd.store_scan_lines[ly][c2a]
        for metal_r in sl.rects:
            if metal_r.rect[o+0] <= c2p//2 <= metal_r.rect[o+2]:
                return metal_r.rect
        assert False

    def _check_metal_rules(self, layer, vv):
        '''Check metal min-length / min-spacing rules'''
        for v in vv.values():
            self._check_min_length(
                layer, v.rects, v.dIndex)
            self._check_min_spacing(
                layer, v.rects, v.dIndex)

    def _check_min_length(self, layer, slrects, dIndex):
        min_length = self.canvas.pdk[layer]['MinL']
        (start, end) = (dIndex, dIndex + 2)
        for slr in slrects:
            rect = slr.rect
            if rect[end] - rect[start] < min_length:
                root = slr.root()
                self.errors.append(
                    f"MinLength violation on {layer}: {root.netName}{rect}")

    def _check_min_spacing(self, layer, slrects, dIndex):
        min_space = self.canvas.pdk[layer]['EndToEnd']
        (start, end) = (dIndex, dIndex + 2)
        prev_slr = None
        for slr in slrects:
            if prev_slr is not None and slr.rect[start] - prev_slr.rect[end] < min_space:
                self.errors.append(
                    f"MinSpace violation on {layer}: {prev_slr.root().netName}{prev_slr.rect} x {slr.root().netName}{slr.rect}")
            prev_slr = slr
        return
