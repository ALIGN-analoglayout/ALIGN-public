
import pathlib

class MetalTemplate:
    def __init__(self, m):
        self.m = m

        self.widths = []
        self.spaces = []
        self.colors = []

        self.offset = None
        self.stops = []
        self.stop_offset = None

        last_c = None
        last_width = None

        for (idx,(c,attrs)) in enumerate(m.clg.grid):
            if idx not in m.clg.legalIndices:
                continue

            if self.offset is None:
                self.offset = c

            (width, color) = attrs

            self.widths.append(width)
            if color is not None:
                self.colors.append( color)

            if last_c is not None:
                pitch = c - last_c
                space = pitch - (last_width + width)//2
                self.spaces.append(space)

            last_c = c
            last_width = width


        last_c = None

        print( "spg", m.spg.grid, m.spg.legalIndices)

        tuples = [ (idx,pair) for (idx,pair) in enumerate(m.spg.grid) if idx in m.spg.legalIndices]
        print( m.spg.grid, tuples)
        if tuples[-1][0] < m.spg.n:
            idx = tuples[0][0]
            attrs = tuples[0][1][1]
            new_tuple = ( idx + m.spg.n, (m.spg.value( (1,idx), attrs)))
            print( "new tuple", new_tuple)
            tuples.append( new_tuple)

        print( "new tuples:", tuples)

        for (idx,(c,attrs)) in tuples:

            if self.stop_offset is None:
                self.stop_offset = c

            print( idx, attrs, c, last_c)

            if last_c is not None:
                if c != last_c:
                    self.stops.append( c - last_c)

            last_c = c

    def write( self, fp):
        m = self.m
        widths = ','.join( [ str(x) for x in self.widths])
        spaces = ','.join( [ str(x) for x in self.spaces])

        colors_str = ""
        if self.colors:
            colors_str = " colors=" + (','.join( self.colors))

        stops = ','.join( [ str(x) for x in self.stops])

        fp.write( f"MetalTemplate layer={m.layer} name={m.nm} widths={widths} spaces={spaces}{colors_str} stops={stops} stop_offset={self.stop_offset}\n")


def write_metal_templates( c, m, fp):
    mt = MetalTemplate(m)
    mt.write( fp)


def gen( c, dirname):
    dirpath = pathlib.Path(dirname)
    dirpath.mkdir( parents=True, exist_ok=True)
    
    print( c.layer_stack)

    for ( v, (m_l, m_u)) in c.layer_stack:
        print( f"Via {v} Metal below {m_l} Metal above {m_u}")

    metal_templates = dict({ (k, v) for (k,v) in c.generators.items() if k.startswith('m') })
    with dirpath.joinpath('metal_templates.txt').open('wt') as fp:
        for (k,v) in metal_templates.items():
            write_metal_templates( c, v, fp)

    for (k,v) in c.generators.items():
        print( k, v)

    return True

