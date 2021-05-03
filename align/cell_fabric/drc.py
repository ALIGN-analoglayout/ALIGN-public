import pprint
import logging
logger = logging.getLogger(__name__)

class RegionSet:
    def __init__(self):
        self.rects = []

    def add_region(self, rect):
        self.rects.append( rect)

    def contained_in( self, rect):
        for r in self.rects:
            if r[0] <= rect[0] and rect[2] <= r[2] and \
               r[1] <= rect[1] and rect[3] <= r[3]:
                #logger.debug( f"Filtering rect {rect} inside {r}")
                return True
        #logger.debug( f"Did not filter rect {rect}: {self.rects}")
        return False
        
class DesignRuleCheck():
    def __init__(self, canvas):
        self.canvas = canvas
        self.errors = []

        self.r_regions = RegionSet()
        for term in self.canvas.terminals:
            if term['layer'] == 'Boundary':
                logger.debug( f"Adding region {term['rect']} using 'Boundary' object")
                self.r_regions.add_region( term['rect'])

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
                self._check_adjacent_metals( layer, vv)

        #SMB Is it good enough to have the actual errors in the .errors file
        if True:
            if self.errors:
                logger.error(f'Found errors: DRC {self.num_errors} ')
            else:
                for error in self.errors:
                    logger.warning(pprint.pformat(error))

        return self.num_errors

    def _check_via_rules(self, layer, vv):
        '''Simple rules related to vertical and horizontal spacing; need more work for diagonals'''
        if 'SpaceY' in self.canvas.pdk[layer]:
            # need a walrus operator
            space_y = self.canvas.pdk[layer]['SpaceY']
            if space_y is not None: 
                # Since vias are stored as vertical wires in the scan lines, this is the easy case 
                # find closest via with same X centerline with higher Y value
                for (_, sl0) in vv.items():
                    for slr0 in sl0.rects:
                        for slr1 in sl0.rects:
                            if slr0 == slr1: continue
                            if slr0.rect[3] < slr1.rect[1]:
                                if slr0.rect[3] + space_y > slr1.rect[1]:
                                    self.errors.append( f"Vertical space violation on {layer}: {slr0} {slr1} {space_y}")
        if 'SpaceX' in self.canvas.pdk[layer]:
            space_x = self.canvas.pdk[layer]['SpaceX']
            if space_x is not None: 
                # This is harder
                # find closest via with same Y coords and with a higher X value
                for (cx0, sl0) in vv.items():
                    for (cx1, sl1) in vv.items():
                        if cx0 >= cx1: continue
                        for slr0 in sl0.rects:
                            for slr1 in sl1.rects:
                                if slr0.rect[1] == slr1.rect[1] and slr0.rect[3] == slr1.rect[3]:
                                    if slr0.rect[2] < slr1.rect[0]:
                                        if slr0.rect[2] + space_x > slr1.rect[0]:
                                            self.errors.append( f"Horizontal space violation on {layer}: {slr0} {slr1} {space_x}")



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
            net_name = r.netName
            if net_name is None: net_name = "None"
            if metal_r is None:
                self.errors.append( f"Enclosure violation on {ly}-{layer} for {net_name}: No metal found surrounding {r.rect}, {enclosure_value}")
            elif metal_r[o+0] > r.rect[o+0] - enclosure_value or metal_r[o+2] < r.rect[o+2] + enclosure_value:
                self.errors.append( f"Enclosure violation on {ly}-{layer} for {net_name}: {metal_r} does not sufficiently surround {r.rect}, {enclosure_value}")

        for _, sl in vv.items():
            for r in sl.rects:
                if ly_l is not None: check_single_metal( r, ly_l, ml_dir, v['VencA_L'])
                if ly_u is not None: check_single_metal( r, ly_u, mu_dir, v['VencA_H'])

    def _check_adjacent_metals( self, layer, vv):
        m = self.canvas.pdk[layer]
        if 'AdjacentAttacker' not in m: return
        
        dist = m['AdjacentAttacker']

        dr = m['Direction'].upper()
        assert dr in ['V','H']

        o = 0 if dr == 'H' else 1

        for cx0,v0 in vv.items():
            for cx1 in [cx0-2*m['Pitch'], cx0+2*m['Pitch']]:
                if cx1 in vv:
                    v1 = vv[cx1]
                    for slr0 in v0.rects:
                        for slr1 in v1.rects:
                            if 0 < slr1.rect[o+0] - slr0.rect[o+2] <= dist:
                                self.errors.append( f"Adjacent metal attacker {layer}: {slr0.rect} too close to {slr1.rect} dist: {dist}")


    def _find_rect_covering_via( self, r, ly, metal_dir):
        cx2 = r.rect[0]+r.rect[2]
        cy2 = r.rect[1]+r.rect[3]
        c2a,c2p,o = (cx2,cy2,0) if metal_dir == 'H' else (cy2,cx2,1)
        sl = self.canvas.rd.store_scan_lines[ly][c2p]

        def binary_search( l, u, v):
            if l == u:
                return None
            elif l+1 == u:
                if sl.rects[l].rect[o+0] <= v <= sl.rects[l].rect[o+2]:
                    return sl.rects[l].rect
                else:
                    return None
            else:
                m = (l+u+1)//2
                if sl.rects[m].rect[o+0] <= v:
                    return binary_search( m, u, v)
                else:
                    return binary_search( l, m, v)

        result = binary_search( 0, len(sl.rects), c2a//2)
        if result is not None:
            return result
        else:
            #assert False, f"No rectangle on {ly} covering via at {r.rect}"
            return result

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
                if self.r_regions.contained_in( rect):
                    logger.debug( f"Skipping: MinLength violation on {layer}: {root.netName}{rect}")
                else:
                    self.errors.append(
                        f"MinLength violation on {layer}: {root.netName}{rect}")

    def _check_min_spacing(self, layer, slrects, dIndex):
        min_space = self.canvas.pdk[layer]['EndToEnd']
        (start, end) = (dIndex, dIndex + 2)
        prev_slr = None
        for slr in slrects:
            if prev_slr is not None and \
               0 < slr.rect[start] - prev_slr.rect[end] < min_space:
                if self.r_regions.contained_in( slr.rect):
                    logger.debug( f"Skipping: MinSpace violation on {layer}: {prev_slr.root().netName}{prev_slr.rect} x {slr.root().netName}{slr.rect}")
                else:
                    self.errors.append(
                        f"MinSpace violation on {layer}: {prev_slr.root().netName}{prev_slr.rect} x {slr.root().netName}{slr.rect}")
            prev_slr = slr
        return
