from align.cell_fabric.routing_collateral import MetalTemplate

from align.cell_fabric.grid import *
from align.cell_fabric.canvas import *

def test_one_third():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = UncoloredCenterLineGrid( width=400, pitch=720)
    m.spg = EnclosureGrid( pitch=720, stoppoint=240)
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400]
    assert mt.spaces == [320]
    assert mt.offset == 0
    assert mt.stop_offset == 240
    assert mt.stops == [240, 480]

def test_one_half():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = UncoloredCenterLineGrid( width=400, pitch=720)
    m.spg = EnclosureGrid( pitch=720, stoppoint=360)
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400]
    assert mt.spaces == [320]
    assert mt.offset == 0
    assert mt.stop_offset == 360
    assert mt.stops == [720]

def test_one_half_alt():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = UncoloredCenterLineGrid( width=400, pitch=720)
    m.spg = Grid()
    m.spg.addGridLine( 0, False)
    m.spg.addGridLine( 360, True)
    m.spg.addGridLine( 720, False)
    m.spg.semantic()
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400]
    assert mt.spaces == [320]
    assert mt.offset == 0
    assert mt.stop_offset == 360
    assert mt.stops == [720]

def test_one_half_alt2():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = UncoloredCenterLineGrid( width=400, pitch=720)
    m.spg = CenteredGrid( pitch=720)
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400]
    assert mt.spaces == [320]
    assert mt.offset == 0
    assert mt.stop_offset == 360
    assert mt.stops == [720]

def test_one_half_with_offset():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = UncoloredCenterLineGrid( width=400, pitch=720)
    m.spg = CenteredGrid( pitch=720, offset=280)
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400]
    assert mt.spaces == [320]
    assert mt.offset == 0
    assert mt.stop_offset == 360+280
    assert mt.stops == [720]

def test_endpoints():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = UncoloredCenterLineGrid( width=400, pitch=720)
    m.spg = Grid()
    m.spg.addGridLine( 0, True)
    m.spg.addGridLine( 720, True)
    m.spg.semantic()
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400]
    assert mt.spaces == [320]
    assert mt.offset == 0
    assert mt.stop_offset == 0
    assert mt.stops == [720]

def test_colors():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = CenterLineGrid()
    m.clg.addCenterLine( 0*720, 400, True, color="red")
    m.clg.addCenterLine( 1*720, 400, True, color="black")
    m.clg.addCenterLine( 2*720, 400, True, color="red")

    m.spg = EnclosureGrid( pitch=720, stoppoint=240)
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400, 400]
    assert mt.spaces == [320, 320]
    assert mt.offset == 0
    assert mt.colors == ["red","black","red"]
    assert mt.stop_offset == 240
    assert mt.stops == [240, 480]

def test_complex():
    m = Wire( 'm1', 'M1', 'v', clg=None, spg=None)
    m.clg = CenterLineGrid()
    m.clg.addCenterLine( 0*720,    400, True, color="red")
    m.clg.addCenterLine( 1*720-80, 400, True, color="black")
    m.clg.addCenterLine( 2*720+80, 400, True, color="black")
    m.clg.addCenterLine( 3*720,    400, True, color="red")

    m.spg = EnclosureGrid( pitch=720, stoppoint=240)
    mt = MetalTemplate(m)

    assert mt.widths == [400, 400, 400, 400]
    assert mt.spaces == [240, 480, 240]
    assert mt.offset == 0
    assert mt.colors == ["red","black","black","red"]
    assert mt.stop_offset == 240
    assert mt.stops == [240, 480]
