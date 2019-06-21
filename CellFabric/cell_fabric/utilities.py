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
            if self.canvas.rd.layers[layer] == '*':
                self._check_via_rules(layer, vv)
            else:
                self._check_metal_rules(layer, vv)
        return self.num_errors

    def _check_via_rules(self, layer, vv):
        '''TODO : Add via pattern checking rules '''
        space = self.canvas.pdk[layer]['SpaceX']
        return space

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
        min_space = self.canvas.pdk[layer]['End-to-End']
        (start, end) = (dIndex, dIndex + 2)
        prev_slr = None
        for slr in slrects:
            if prev_slr is not None and slr.rect[start] - prev_slr.rect[end] < min_space:
                self.errors.append(
                    f"MinSpace violation on {layer}: {prev_slr.root().netName}{prev_slr.rect} x {slr.root().netName}{slr.rect}")
            prev_slr = slr
        return


class ParasiticExtraction():
    def __init__(self, canvas):
        self.canvas = canvas

    def run(self):
        raise NotImplementedError("Work in Progress")
