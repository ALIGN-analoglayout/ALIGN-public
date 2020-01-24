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
        [ml,mu] = [self.canvas.pdk[ly] for ly in [ly_l,ly_u]]
        assert ml['Direction'].upper() in ['V','H']
        assert mu['Direction'].upper() in ['V','H']

        for c2, sl in vv.items():
            for r in sl.rects:
                cx2 = r.rect[0]+r.rect[2]
                cy2 = r.rect[1]+r.rect[3]
                
                idx,o = (cx2,1) if ml['Direction'].upper() == 'V' else (cy2,0)
                # find rect covering via
                l_sl = self.canvas.rd.store_scan_lines[ly_l][idx]
                assert len(l_sl.rects) == 1
                metal_r = l_sl.rects[0].rect
                # check enclosure rules
                if metal_r[o+0] > r.rect[o+0] - v['VencA_L'] or metal_r[o+2] < r.rect[o+2] + v['VencA_L']:
                    self.errors.append( f"Enclosure error: {metal_r} does not sufficiently surround {r.rect}")

                idx,o = (cx2,1) if mu['Direction'].upper() == 'V' else (cy2,0)
                # find rect covering via
                u_sl = self.canvas.rd.store_scan_lines[ly_u][idx]
                assert len(u_sl.rects) == 1
                metal_r = u_sl.rects[0].rect
                # check enclosure rules
                if metal_r[o+0] > r.rect[o+0] - v['VencA_H'] or metal_r[o+2] < r.rect[o+2] + v['VencA_H']:
                    self.errors.append( f"Enclosure error: {v} {metal_r} does not sufficiently surround {r.rect}")


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
