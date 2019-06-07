import json
import logging

class DesignRuleCheck():
    def __init__(self, canvas):
        self.canvas = canvas

    def run(self):
        '''
        Run DRC on self.canvas & report errors if any

        Note: self.canvas must already contain 'rd'
              (aka removeDuplicates has been run)
        '''

        self.num_errors = 0
        for (layer, vv) in self.canvas.rd.store_scan_lines.items():
            if self.canvas.rd.layers[layer] == '*':
                self._check_via_rules(layer, vv)
            else:
                self._check_metal_rules(layer, vv)
        return self.num_errors

    def _check_via_rules(self, layer, vv):
        '''TODO : Add via pattern checking rules '''
        return

    def _check_metal_rules(self, layer, vv):
        '''Check metal min-length / min-spacing rules'''
        for v in vv.values():
            self._check_min_length(
                layer, v.rects, self.canvas.rd.layers[layer])
            self._check_min_spacing(
                layer, v.rects, self.canvas.rd.layers[layer])

    def _check_min_length(self, layer, slrects, direction):
        min_length = self.canvas.pdk[layer]['MinL']
        (l, u) = (0, 2) if direction == 'h' else (1, 3)
        for slr in slrects:
            rect = slr.rect
            if rect[u] - rect[l] < min_length:
                root = slr.root()
                logging.error(
                    f"MinLength violation on layer:{layer} position:{rect} net:{root.netName}")
                self.num_errors += 1

    def _check_min_spacing(self, layer, slrects, direction):
        min_space = self.canvas.pdk[layer]['End-to-End']
        (l, u) = (0, 2) if direction == 'h' else (1, 3)
        prev_slr = None
        for slr in slrects:
            if prev_slr is not None and slr.rect[l] - prev_slr.rect[u] < min_space:
                if direction == 'h':
                    space_rect = ( prev_slr.rect[2], prev_slr.rect[1], slr.rect[0], slr.rect[3] )
                else:
                    space_rect = ( prev_slr.rect[0], prev_slr.rect[3], slr.rect[2], slr.rect[1] )
                logging.error(
                    f"MinSpace violation on layer:{layer} position:{space_rect} net1:{prev_slr.root().netName}, net2:{slr.root().netName}]")
                self.num_errors += 1
            prev_slr = slr
        return


class ParasiticExtraction():
    def __init__(self, canvas):
        self.canvas = canvas

    def run(self):
        raise NotImplementedError("Work in Progress")
