#!/usr/bin/env python

import re
from collections import namedtuple
from collections import OrderedDict
import json

Point = namedtuple('Point', ['x', 'y'])
Rect = namedtuple('Rect', ['ll', 'ur'])
Port = namedtuple('Port', ['port_nm', 'layer', 'rect'])
Blockage = namedtuple('Blockage', ['layer', 'rect'])
Terminal = namedtuple('Terminal', ['net_nm', 'layer'])

class Placement:
    def __init__( self):
        self.die = None
        self.block_placement = OrderedDict()
        self.net_wire_lengths = []

    def __repr__( self):
        return 'Placement(' + str(self.die) + "," + str(self.block_placement) + "," + str(self.net_wire_lengths) + ')'


    def semantic( self):
        assert self.die is not None
        assert self.die.ll.x <= self.die.ur.x
        assert self.die.ll.y <= self.die.ur.y


    def parse( self, fp):
        p_comment = re.compile( r'^#.*$')
        p_blank = re.compile( r'^\s*$')
        p_die = re.compile( r'^DIE\s*'
                            r'{\s*(-?\d+)\s*,\s*(-?\d+)\s*}'
                            r'\s*'
                            r'{\s*(-?\d+)\s*,\s*(-?\d+)\s*}'
                            r'\s*$')

        p_triple = re.compile( r'^(\S+)\s+(\S+)\s+(\S+)\s*$')
        p_quadruple = re.compile( r'^(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*$')

        for line in fp:
            line = line.rstrip( '\n')
            m = p_comment.match(line)
            if m: continue
            m = p_blank.match(line)
            if m: continue
            m = p_die.match(line)
            if m:
                self.die = Rect( Point( int(m.groups()[0]), int(m.groups()[1])), Point( int(m.groups()[2]), int(m.groups()[3])))
                continue
            m = p_triple.match(line)
            if m:
                self.net_wire_lengths.append( ( m.groups()[0], Point( int(m.groups()[1]), int(m.groups()[2]))))
                continue
            m = p_quadruple.match(line)
            if m:
                self.block_placement[m.groups()[0]] = ( m.groups()[0], Point( int(m.groups()[1]), int(m.groups()[2])), m.groups()[3])
                continue
            assert False, line

class Constraint:
    def __init__( self):
        pass


class SymmNet(Constraint):
    def __init__( self):
        pass

    def __repr__( self):
        return "SymmNet(" + str( self.lst0) + "," + str( self.lst1) + ")"

    def semantic( self):
        assert len(self.lst0) >= 2
        assert len(self.lst1) >= 2

class CritNet(Constraint):
    def __init__( self):
        pass

    def __repr__( self):
        return "CritNet(" + self.net_nm + "," + self.level + ")"

    def semantic( self):
        assert self.level in ['mid','min']

class ShieldNet(Constraint):
    def __init__( self):
        pass

    def __repr__( self):
        return "ShieldNet(" + ")"

    def semantic( self):
        pass


class MatchBlock(Constraint):
    def __init__( self):
        pass

    def __repr__( self):
        return "MatchBlock(" + ")"

    def semantic( self):
        pass


class Constraints:
    def __init__( self):
        self.constraints = []

    def __repr__( self):
        return ','.join( [ str(x) for x in self.constraints])

    def semantic( self):
        for c in self.constraints:
            c.semantic()

    def parse( self, fp):
        p_comment = re.compile( r'^#.*$')
        p_blank = re.compile( r'^\s*$')
        p_constraint = re.compile( r'^(SymmNet|CritNet|ShieldNet|MatchBlock)'
                                   r'\s*\('
                                   r'(.*)'
                                   r'\)\s*$')

        p_bracecommasep = re.compile( r'^{(.+)}\s*,\s*{(.+)}$')
        p_commasep = re.compile( r'^(\S+)\s*,\s*(\S+)$')
        p_pin = re.compile( r'^(.+)/(.+)$')


        def toLst( s):
            lst = s.split(',')
            assert len(lst) >= 2, lst
            result = lst[0:1]
            for e in lst[1:]:
                m = p_pin.match( e)
                if m:
                    block_nm = m.groups()[0]
                    formal_nm = m.groups()[1]
                    result.append( ( block_nm, formal_nm))
                    continue
                result.append( ( 'terminal', e))
            return result


        for line in fp:
            line = line.rstrip( '\n')

            m = p_comment.match(line)
            if m: continue
            m = p_blank.match(line)
            if m: continue
            m = p_constraint.match(line)
            if m:
                tag = m.groups()[0]
                rest = m.groups()[1].strip( ' ')
                if   tag == 'SymmNet':
                    c = SymmNet()

                    mm = p_bracecommasep.match( rest)
                    assert mm, rest

                    c.lst0 = toLst( mm.groups()[0])
                    c.lst1 = toLst( mm.groups()[1])

                elif tag == 'CritNet':
                    c = CritNet()

                    mm = p_commasep.match( rest)
                    assert mm, rest

                    c.net_nm = mm.groups()[0]
                    c.level = mm.groups()[1]

                elif tag == 'ShieldNet':
                    c = ShieldNet()
                    pass
                elif tag == 'MatchBlock':
                    c = MatchBlock()
                    pass
                else:
                    assert False

                self.constraints.append( c)

                continue

            assert False, line



class Net:
    def __init__( self):
        self.net_nm = None
        self.pin_count = None
        self.pin_lst = []

    def __repr__( self):
        return "Net(" + self.net_nm + "," + str(self.pin_count) + "," + str(self.pin_lst) + ")"

class Netlist:
    def __init__( self):
        self.params = OrderedDict()
        self.nets = OrderedDict()

        self.pins = {}


    def __repr__( self):
        return "Netlist(" + str(self.params) + "," + str(self.nets) + ")"

    def semantic( self):
        assert self.params['NumNets'] == len(self.nets)
        nPins = sum( [ len([ x for x in v.pin_lst if x[0] != 'terminal']) for (k,v) in self.nets.items()])
        assert self.params['NumPins'] == nPins, (self.params['NumPins'], nPins)
        for (k,v) in self.nets.items():
            assert v.pin_count is not None, k
            assert v.pin_count == len(v.pin_lst), (k, v.pin_count, len(v.pin_lst))

            for pin in v.pin_lst:
                assert pin not in self.pins, (k, pin,'not in',self.pins)
                self.pins[pin] = k

    def parse( self, fp):
        p_comment = re.compile( r'^#.*$')
        p_blank = re.compile( r'^\s*$')
        p_assignments = re.compile( r'^(NumNets|NumPins)\s*:\s*(\d+)\s*$')
        p_net_and_count = re.compile( r'^(\S+)\s*:\s*(\d+)\s*$')
        p_pairs = re.compile( r'^(\S+)\s+(\S+)\s*$')

        net = None
        for line in fp:
            line = line.rstrip( '\n')

            m = p_comment.match(line)
            if m: continue
            m = p_blank.match(line)
            if m: continue
            m = p_assignments.match(line)
            if m:
                self.params[m.groups()[0]] = int(m.groups()[1])
                continue
            m = p_net_and_count.match(line)
            if m:
                net = Net()
                net.net_nm = m.groups()[0]
                net.pin_count = int(m.groups()[1])
                self.nets[net.net_nm] = net
                continue
            m = p_pairs.match(line)
            if m:
                net.pin_lst.append( (m.groups()[0], m.groups()[1]))
                continue
            assert False, line
            

class Block:
    def __init__( self, nm):
        self.nm = nm
        self.rect = None
        self.port_count = None
        self.port_lst = []
        self.blockage_lst = []

    def __repr__( self):
        return 'Block(' + self.nm + "," + str(self.port_count) + "," + str(self.port_lst) + ')'

    def semantic( self):
        assert self.port_count is not None
        assert self.port_count == len(self.port_lst), (self.port_count, len(self.port_lst))

class Blocks:
    def __init__( self):
        self.params = {}
        self.block_lst = OrderedDict()
        self.terminal_lst = []
    
    def __repr__( self):
        return 'Blocks(' + str(self.params) + "," + str(self.block_lst) + "," + str(self.terminal_lst) + ')'

    def semantic( self):
        assert self.params['NumSoftRectangularBlocks'] == 0
        assert self.params['NumHardRectilinearBlocks'] == len(self.block_lst)
        assert self.params['NumTerminals'] == len(self.terminal_lst)
        for (k,v) in self.block_lst.items():
            v.semantic()

    def parse( self, fp):
        p_comment = re.compile( r'^#.*$')
        p_blank = re.compile( r'^\s*$')

        p_assignments = re.compile( r'^(NumSoftRectangularBlocks|NumHardRectilinearBlocks|NumTerminals)\s*:\s*(\d+)\s*$')

        p_outline = re.compile( r'^(\S+)\s+(hardrectilinear)\s+'
                                r'(\d+)\s+'
                                r'((\(\s*(-?\d+)\s*\,\s*(-?\d+)\s*\)\s*)*)'
                                r'$')


        p_block = re.compile( r'^BLOCK\s+(\S+)\s*:\s*(\d+)\s*$')

        p_port = re.compile( r'^(\S+)\s+(\S+)\s+'
                            r'((\(\s*(-?\d+)\s*\,\s*(-?\d+)\s*\)\s*){4})'
                            r'$')

        p_terminal = re.compile( r'^(\S+)\s+(\S+)\s+terminal\s*$')


        p_pair = re.compile( r'^\s*\(\s*(-?\d+)\s*,\s*(-?\d+)\s*\)(.*)$')

        def parse_pair_list( s):
            result = []
            rest = s
            while True:
                m = p_blank.match( rest)
                if m: return result
                m = p_pair.match( rest)
                assert m, rest
                x = int(m.groups()[0])
                y = int(m.groups()[1])
                rest = m.groups()[2]
                result.append( Point(x=x,y=y))


        block = None
        if True:
            for line in fp:
                line = line.rstrip('\n')
                m = p_comment.match(line)
                if m: continue
                m = p_blank.match(line)
                if m: continue
                m = p_assignments.match(line)
                if m:
                    self.params[m.groups()[0]] = int(m.groups()[1])
                    continue
                m = p_outline.match(line)
                if m:
                    block_nm = m.groups()[0]
                    block = Block( block_nm)
                    type_nm = m.groups()[1]
                    point_count = int(m.groups()[2])
                    point_lst = parse_pair_list( m.groups()[3])
                    assert point_count == len(point_lst)
                    assert point_count == 4

                    rect = Rect( ll=point_lst[0], ur=point_lst[2])

                    for p in point_lst:
                        assert rect.ll.x <= p.x
                        assert rect.ll.y <= p.y
                        assert rect.ur.x >= p.x
                        assert rect.ur.y >= p.y

                    block.rect = rect

                    self.block_lst[block_nm] = block

                    block = None

                    continue
                m = p_block.match(line)
                if m:
                    block_nm = m.groups()[0]
                    assert block_nm in self.block_lst
                    block = self.block_lst[block_nm]
                    block.port_count = int(m.groups()[1])
                    continue
                m = p_port.match(line)
                if m:
                    port_nm = m.groups()[0]
                    layer = m.groups()[1]
                    point_lst = parse_pair_list( m.groups()[2])
                    assert len(point_lst) == 4

                    rect = Rect( ll=point_lst[0], ur=point_lst[2])

                    for p in point_lst:
                        pass
#                        assert rect.ll.x <= p.x, (p, 'should be inside', rect)
#                        assert rect.ll.y <= p.y, (p, 'should be inside', rect)
#                        assert rect.ur.x >= p.x, (p, 'should be inside', rect)
#                        assert rect.ur.y >= p.y, (p, 'should be inside', rect)


                    if port_nm == 'INT':
                        blockage = Blockage( layer, rect)
                        block.blockage_lst.append( port)
                    else:
                        port = Port( port_nm, layer, rect)
                        block.port_lst.append( port)

                    continue
                m = p_terminal.match(line)
                if m:
                    net_nm = m.groups()[0]
                    layer = m.groups()[1]
                    self.terminal_lst.append( Terminal( net_nm, layer))
                    continue

                assert False, line

import io

def test_n3():
    s = """#UMN blocks 1.0
# Created      : July 09 19:15:43
# User         : kunal001@umn.edu
# Platform     : Linux

NumSoftRectangularBlocks : 0
NumHardRectilinearBlocks : 3
NumTerminals : 5

L1_MM4_MM5	hardrectilinear 4 (0, 0) (0, 789) (648, 789) (648, 0)
L1_MM1_MM0	hardrectilinear 4 (0, 0) (0, 842) (648, 842) (648, 0)
L1_MM3_MM2	hardrectilinear 4 (0, 0) (0, 789) (648, 789) (648, 0)


BLOCK L1_MM4_MM5 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (196, 748)	(196,	788)	(236, 788)	(236,	748)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789)	(196, 789)
INT M1 (412, 619) (412, 789) (452, 789)	(412, 789)



BLOCK L1_MM1_MM0 : 5
G1	M1 (108, 684)	(108,	842)	(148, 842)	(148,	684)
G2	M1 (504, 684)	(504,	836)	(544, 836)	(544,	684)
D1	M1 (88,   4)	(88,   146)	(128, 146)	(128,	4)
S	M1 (236, 796)	(236,	836)	(412, 836)	(412,	796)
D2	M1 (520,   0)	(520,	146)	(560, 146)	(560,	0)
INT M1 (196, 612) (196,	836) (236, 836)	(196, 836)
INT M1 (412, 612) (412,	836) (452, 836)	(412, 836)



BLOCK L1_MM3_MM2 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (236, 749)	(236,	789)	(412, 789)	(412,	749)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789) (236, 619)
INT M1 (412, 619) (412, 789) (452, 789) (452, 619)
INT M1 (89, 39) (89, 148) (125, 148) (125, 39)
INT M1 (89, 39) (89, 75) (471, 75) (471, 39)


gnd!	M1 terminal
vdd!	M1 terminal
net2	M1 terminal
net14	M1 terminal
net17	M1 terminal
"""

    with io.StringIO(s) as fp:
        blocks = Blocks()
        blocks.parse( fp)
        blocks.semantic()

def test_negative():

    s = """#UMN blocks 1.0
# Created      : July 09 19:15:43
# User         : kunal001@umn.edu
# Platform     : Linux

NumSoftRectangularBlocks : 0
NumHardRectilinearBlocks : 3
NumTerminals : 5

L1_MM4_MM5	hardrectilinear 4 (0, 0) (0, 789) (648, 789) (648, 0)
L1_MM1_MM0	hardrectilinear 4 (0, 0) (-0, 842) (648, 842) (648, 0)
L1_MM3_MM2	hardrectilinear 4 (-0, 0) (0, 789) (648, 789) (648, 0)


BLOCK L1_MM4_MM5 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (196, 748)	(196,	788)	(236, 788)	(236,	748)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789)	(196, 789)
INT M1 (412, 619) (412, 789) (452, 789)	(412, 789)



BLOCK L1_MM1_MM0 : 5
G1	M1 (108, 684)	(108,	842)	(148, 842)	(148,	684)
G2	M1 (504, 684)	(504,	836)	(544, 836)	(544,	684)
D1	M1 (88,   4)	(88,   146)	(128, 146)	(128,	4)
S	M1 (236, 796)	(236,	836)	(412, 836)	(412,	796)
D2	M1 (520,   -0)	(520,	146)	(560, 146)	(560,	0)
INT M1 (196, 612) (196,	836) (236, 836)	(196, 836)
INT M1 (412, 612) (412,	836) (452, 836)	(412, 836)



BLOCK L1_MM3_MM2 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (236, 749)	(236,	789)	(412, 789)	(412,	749)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789) (236, 619)
INT M1 (412, 619) (412, 789) (452, 789) (452, 619)
INT M1 (89, 39) (89, 148) (125, 148) (125, 39)
INT M1 (89, 39) (89, 75) (471, 75) (471, 39)


gnd!	M1 terminal
vdd!	M1 terminal
net2	M1 terminal
net14	M1 terminal
net17	M1 terminal
"""

    with io.StringIO(s) as fp:
        blocks = Blocks()
        blocks.parse( fp)
        blocks.semantic()


def test_shortened():
    s = """#UMN blocks 1.0
# Created      : July 09 19:15:43
# User         : kunal001@umn.edu
# Platform     : Linux

NumSoftRectangularBlocks : 0
NumHardRectilinearBlocks : 1
NumTerminals : 0

L1_MM4_MM5	hardrectilinear 4 (0, 0) (0, 789) (648, 789) (648, 0)

BLOCK L1_MM4_MM5 : 3
D1	M1 (520, 615)	(520,	761)	(560, 761)	(560,	615)
S	M1 (196, 748)	(196,	788)	(236, 788)	(236,	748)
D2	M1 (88, 615)	(88,   757)	(128, 757)	(128,	615)
INT M1 (196, 619) (196, 789) (236, 789)	(196, 789)
INT M1 (412, 619) (412, 789) (452, 789)	(412, 789)
"""

    with io.StringIO(s) as fp:
        blocks = Blocks()
        blocks.parse( fp)
        blocks.semantic()


def test_net():
    s = """#UMN nets 1.0
# Created      : July 09 19:15:43
# User         : kunal001@umn.edu
# Platform     : Linux

NumNets : 8
NumPins : 11

net2 : 2
L1_MM3_MM2 D1
terminal net2
net8 : 2
L1_MM4_MM5 D1
L1_MM1_MM0 D1
net10 : 2
L1_MM3_MM2 D2
L1_MM1_MM0 S
net11 : 2
L1_MM4_MM5 D2
L1_MM1_MM0 D2
net14 : 2
terminal net14
L1_MM1_MM0 G2
net17 : 2
terminal net17
L1_MM1_MM0 G1
gnd! : 2
L1_MM3_MM2 S
terminal gnd!
vdd! : 2
L1_MM4_MM5 S
terminal vdd!
"""

    with io.StringIO(s) as fp:
        nl = Netlist()
        nl.parse( fp)
        nl.semantic()
    


def test_consts():
    s = """SymmNet ( {net8,L1_MM1_MM0/D1,L1_MM4_MM5/D1} , {net11,L1_MM1_MM0/D2,L1_MM4_MM5/D2} )
SymmNet ( {net17,L1_MM1_MM0/G1,net17} , {net14,L1_MM1_MM0/G2,net14} )
CritNet ( net8 , min )
CritNet ( net10 , mid )
"""

    with io.StringIO(s) as fp:
        cs = Constraints()
        cs.parse( fp)
        cs.semantic()
        print( cs)

def test_pl():
    s = """# TAMU blocks 1.0

DIE {0, 0} {648, 2620}

L1_MM4_MM5	0	0	N
L1_MM1_MM0	648	889	FN
L1_MM3_MM2	0	2620	FS

net2	648	1932
net14	0	1649
net17	648	1652
gnd!	0	1851
vdd!	0	768
"""

    with io.StringIO(s) as fp:
        p = Placement()
        p.parse( fp)
        p.semantic()
        print( p)

class Design:
    def __init__(self):
        pass

    def parse( self, ibasename, obasename):
        with open( ibasename + '.blocks', 'rt') as fp:
            self.blocks = Blocks()
            self.blocks.parse( fp)
            self.blocks.semantic()

        with open( ibasename + '.nets', 'rt') as fp:
            self.nl = Netlist()
            self.nl.parse( fp)
            self.nl.semantic()

        with open( ibasename + '.const', 'rt') as fp:
            self.cs = Constraints()
            self.cs.parse( fp)
            self.cs.semantic()

        with open( obasename + '.pl', 'rt') as fp:
            self.p = Placement()
            self.p.parse( fp)
            self.p.semantic()

    def write_json_for_viewer( self, fp):
        """Write out bbox for instances as well as terminals
Need:
        bbox -- [llx,lly,urx,ury]
        globalRoutes -- []
        globalRouteGrid -- []
        terminals -- each in array { 'netName': , 'layer': , 'gid': , 'rect': [llx,lly,urx,ury]} 
"""
        d = {}

        d['bbox'] = [self.p.die.ll.x, self.p.die.ll.y, self.p.die.ur.x, self.p.die.ur.y]

        d['cellBoundaries'] = []

        d['globalRoutes'] = []
        d['globalRouteGrid'] = []
        d['terminals'] = []

        def translateLayer( layer):
            if layer == 'M1':
                return 'metal1'
            else:
                assert False, layer

        # fake terminal for diearea
        dd = {}
        dd['netName'] = 'top'
        dd['layer'] = 'diearea'
        dd['gid'] = -1
        dd['rect'] = d['bbox']

        d['terminals'].append( dd)



        for (nm,block) in self.blocks.block_lst.items():
            assert nm == block.nm
            plc = self.p.block_placement[block.nm]
            o = plc[1]
            flip = plc[2]

            sx,sy = 1,1
            if   flip == 'FN': # apparently means mirror across y axis; origin at top left
                sx = -1
            elif flip == 'FS': # apparently means mirror across x axis; origin at bot right
                sy = -1
            elif flip == 'S': # apparently means mirror across both x and y axes; origin at top right
                sx,sy = -1,-1
            elif flip == 'N': # no flip
                pass
            else:
                assert False, flip

            def hit( x, y):
                return x*sx+o.x, y*sy+o.y

            def transformRect( r):
                llx,lly = hit( r.ll.x, r.ll.y)
                urx,ury = hit( r.ur.x, r.ur.y)

                # Make sure the rectangles are not empty
                if llx > urx: urx,llx = llx,urx
                if lly > ury: ury,lly = lly,ury

                return [llx,lly,urx,ury]

            r = block.rect

            # fake terminal for cell area
            dd = {}
            dd['netName'] = block.nm
            dd['layer'] = 'cellarea'
            dd['gid'] = -1
            dd['rect'] = transformRect( r)

            d['terminals'].append( dd)

            for port in block.port_lst:
                r = port.rect

                formal = port.port_nm
                actual = self.nl.pins[ (block.nm, formal)]

                dd = {}
                dd['netName'] = actual
                dd['layer'] = translateLayer( port.layer)
                dd['gid'] = -1
                dd['rect'] = transformRect( r)
               
                d['terminals'].append( dd)


        json.dump(d, fp, sort_keys=True, indent=4)
        fp.write( '\n')

    def print( self):
        print( self.blocks)
        print( self.nl)
        print( self.cs)
        print( self.p)


import argparse

if __name__ == "__main__":

    parser = argparse.ArgumentParser( description="Reads results of Placement/Placer and generates a JSON file for the Viewer")

    parser.add_argument( "-n", "--block_name", type=str, default="n3")
    parser.add_argument( "-id", "--input_dir", type=str, default="../Placement/testcase")
    parser.add_argument( "-od", "--output_dir", type=str, default="../Placement/testcase")
    parser.add_argument( "-j", "--json_output_file", type=str, default="../Viewer/INPUT/mydesign_dr_globalrouting.json")

    args = parser.parse_args()

    block_name = args.block_name

    design = Design()
    design.parse( args.input_dir + '/' + block_name, args.output_dir + '/' + block_name)

    with open( args.json_output_file, 'wt') as fp:
        design.write_json_for_viewer( fp)
    
