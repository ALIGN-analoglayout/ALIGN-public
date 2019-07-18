from collections import defaultdict

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
            if layer not in self.canvas.pdk:
                continue
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
        min_space = self.canvas.pdk[layer]['EndToEnd']
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
        self._ports = defaultdict(lambda: defaultdict(list)) # layer: {clg: [spg, spg, spg]}
        self.netCells = [] # (type, startnode, endnode)

    def run(self):
        '''
        Run PEX on self.canvas

        Note: self.canvas must already contain 'rd'
              (aka removeDuplicates has been run)
        '''

        for (layer, vv) in self.canvas.rd.store_scan_lines.items():
            if self.canvas.rd.layers[layer] == '*':
                self._compute_port_locations(layer, vv)

        for (layer, vv) in self.canvas.rd.store_scan_lines.items():
            if layer not in self.canvas.pdk:
                continue
            if self.canvas.rd.layers[layer] == '*':
                self._extract_via_parasitics(layer, vv)
            else:
                self._extract_metal_parasitics(layer, vv)
        return self.netCells

    def _stamp_port(self, layer, x0, x1):
        if layer is None:
            return
        if 'Direction' not in self.canvas.pdk[layer] or self.canvas.pdk[layer]['Direction'] == 'v':
            self._ports[layer][x1].append(x0)
        else:
            self._ports[layer][x0].append(x1)

    def _compute_port_locations(self, layer, vv):
        for x1, v in vv.items():
            for slr in v.rects:
                rect = slr.rect
                x0 = ( rect[v.dIndex] + rect[v.dIndex + 2] ) // 2
                self._stamp_port(layer, x0, x1)
                self._stamp_port(self.canvas.pdk[layer]['Stack'][0], x0, x1)
                self._stamp_port(self.canvas.pdk[layer]['Stack'][1], x0, x1)

    def _extract_via_parasitics(self, layer, vv):
        pass

    def _flatten(self, i):
        if isinstance(i, int):
            return int
        else:
            return '_'.join([str(x) for x in i])

    def _gen_netcell_node_name(self, net, layer, starti, endi):
        return f'{net}_{layer}_{self._flatten(starti)}_{self._flatten(endi)}'

    def _extract_metal_parasitics(self, layer, vv):
        for v in vv.values():
            self._extract_line_parasitics(layer, v.rects, v.dIndex)

    def _extract_line_parasitics(self, layer, slrects, dIndex):
        (start, end) = (dIndex, dIndex + 2)
        for slr in slrects:
            pass
