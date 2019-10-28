import collections
import math

class ParasiticExtraction():
    def __init__(self, canvas):
        self.canvas = canvas
        self._terms = collections.defaultdict(lambda: collections.defaultdict(list)) # layer: {scanline: [p1...pn]}
        self._c_count = 0
        self._r_count = 0
        self.netCells = collections.OrderedDict() # (node1, node2) : (layer, rect)
        self.components = []

    def run(self):
        '''
        Run PEX on self.canvas

        Note: self.canvas must already contain 'rd'
              (aka removeDuplicates has been run)
        '''

        # Compute Via intersections with metal lines
        for (layer, vv) in self.canvas.rd.store_scan_lines.items():
            if self.canvas.rd.layers[layer] == '*':
                self._compute_via_intersections(layer, vv)

        # Topological sort is not needed since coordinates are already sorted
        # [ x.sort() for vv in self._terms.values() for x in vv.values() ]

        # Create OrderedDict with NodeName -> layer, rect mappings
        for (layer, vv) in self.canvas.rd.store_scan_lines.items():
            if layer not in self.canvas.pdk:
                continue
            if self.canvas.rd.layers[layer] == '*':
                self._extract_via_parasitics(layer, vv)
            else:
                self._extract_metal_layer(layer, vv)

        # Stamp out R, C components
        # mode = "Tee"
        mode = "Pi"
        for tup in self.netCells.items():
            ((t0,t1),(ly,rect)) = tup
            if ly.startswith('M'):
                dist = self.compute_dist( rect[0], rect[2]) \
                        if self.canvas.pdk[ly]['Direction'] == 'h' \
                        else self.compute_dist( rect[1], rect[3])
                (self.pi if mode == "Pi" else self.tee)( t0, t1, self.canvas.pdk[ly]['UnitR']*dist, self.canvas.pdk[ly]['UnitC']*dist )
            elif ly.startswith('V'):
                self.components.append( (self.resistor(), t0, t1, self.canvas.pdk[ly]['R']))
            else:
               assert False, ly

    def _stamp_port(self, layer, x0, x1):
        if layer is None:
            return
        if self.canvas.rd.layers[layer] == 'h':
            if x1 not in self._terms[layer][x0 * 2]:
                self._terms[layer][x0 * 2].append(x1)
        else:
            if x0 not in self._terms[layer][x1 * 2]:
                self._terms[layer][x1 * 2].append(x0)

    def _compute_via_intersections(self, layer, vv):
        for twice_center, v in vv.items():
            for slr in v.rects:
                rect = slr.rect
                x0 = ( rect[v.dIndex] + rect[v.dIndex + 2] ) // 2
                x1 = twice_center // 2
                self._stamp_port(layer, x0, x1)
                self._stamp_port(self.canvas.pdk[layer]['Stack'][0], x0, x1)
                self._stamp_port(self.canvas.pdk[layer]['Stack'][1], x0, x1)

    def _extract_via_parasitics(self, layer, vv):
        for v in vv.values():
            for slr in v.rects:
                self._create_via_netcells(slr.root().netName, slr.terminal, layer, slr.rect)

    def _create_via_netcells(self, net, terminal, layer, rect):
        x = ( rect[0] + rect[2] ) // 2
        y = ( rect[1] + rect[3] ) // 2
        if terminal is None:
            node1 = self._gen_netcell_node_name(net, self.canvas.pdk[layer]['Stack'][0], x, y)
            node2 = self._gen_netcell_node_name(net, self.canvas.pdk[layer]['Stack'][1], x, y)
        elif self.canvas.pdk[layer]['Stack'][0] is None:
            node1 = f'{terminal[0].replace("/", "_")}_{terminal[1]}'
            node2 = self._gen_netcell_node_name(net, self.canvas.pdk[layer]['Stack'][1], x, y)
        else:
            raise NotImplementedError
        self.netCells[ (node1, node2) ] = (layer, rect)

    @staticmethod
    def _gen_netcell_node_name(net, layer, x, y):
        return f'{net}_{layer}_{x}_{y}'.replace('-', '_')

    def _extract_metal_layer(self, layer, vv):
        for twice_center, v in vv.items():
            self._extract_metal_scanline(layer, v.rects, v.dIndex, twice_center)

    def _extract_metal_scanline(self, layer, slrects, dIndex, twice_center):
        for slr in slrects:
            self._extract_metal_rectangle(slr.root().netName, layer, twice_center, slr.rect, dIndex)

    def _stamp_netcells(self, net, layer, twice_center, starti, endi, rect, dIndex):
        numcells = math.ceil( (endi - starti) / self.canvas.pdk['Poly']['Pitch'] )
        for i in range(numcells):
            cellstart = starti + i * self.canvas.pdk['Poly']['Pitch']
            if i == numcells - 1:
                cellend = endi
            else:
                cellend = cellstart + self.canvas.pdk['Poly']['Pitch']
            if self.canvas.pdk[layer]['Direction'] == 'v':
                node1 = self._gen_netcell_node_name(net, layer, twice_center // 2, cellstart)
                node2 = self._gen_netcell_node_name(net, layer, twice_center // 2, cellend)
            else:
                node1 = self._gen_netcell_node_name(net, layer, cellstart, twice_center // 2)
                node2 = self._gen_netcell_node_name(net, layer, cellend, twice_center // 2)
            cell_rect = rect.copy()
            cell_rect[dIndex] = cellstart
            cell_rect[dIndex + 2] = cellend
            self.netCells[ (node1, node2) ] = (layer, cell_rect)
        return endi

    def _extract_metal_rectangle(self, net, layer, twice_center, rect, dIndex):
        (starti, endi) = (rect[dIndex], rect[dIndex + 2])
        prev_port = None
        for port in self._terms[layer][twice_center]:
            if prev_port is None:
                if port > starti:
                    prev_port = self._stamp_netcells(net, layer, twice_center, starti, port, rect, dIndex)
            elif port > endi:
                break
            else:
                prev_port = self._stamp_netcells(net, layer, twice_center, prev_port, port, rect, dIndex)
        if prev_port is None:
            prev_port = starti
        self._stamp_netcells(net, layer, twice_center, prev_port, endi, rect, dIndex)

    def resistor(self):
        result = f"r{self._r_count}"
        self._r_count += 1
        return result

    def capacitor(self):
        result = f"c{self._c_count}"
        self._c_count += 1
        return result

    @staticmethod
    def compute_dist(p, q):
        return abs(p - q)/1000

    def pi( self, t0, t1, R, C):
        self.components.append( (self.resistor(), t0, t1, R))
        self.components.append( (self.capacitor(), t0, 0, C/2))
        self.components.append( (self.capacitor(), t1, 0, C/2))

    def tee( self, t0, t1, R, C):
        tm = t0+t1
        self.components.append( (self.resistor(), t0, tm, R/2))
        self.components.append( (self.resistor(), tm, t1, R/2))
        self.components.append( (self.capacitor(), tm, 0, C))

    def writePex(self, fp):
        for tup in self.components:
            if tup[0][0] == 'r':
                (nm, t0, t1, v) = tup
                fp.write( f"{nm} {t0} {t1} {v}\n")
            elif tup[0][0] == 'c':
                (nm, t0, t1, v) = tup
                fp.write( f"{nm} {t0} {t1} {v}f\n")
            else:
                assert False

        for inst, _ in self.canvas.rd.subinsts.items():
            inst = inst.replace("/", "_")
            fp.write( f"{inst}_0 {inst}_D {inst}_G {inst}_diff w={{width}} l={{length}} nfin={{nfin}}\n")
            fp.write( f"{inst}_1 {inst}_diff {inst}_G {inst}_S w={{width}} l={{length}} nfin={{nfin}}\n")