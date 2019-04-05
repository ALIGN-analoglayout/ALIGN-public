
from cktgen import techfile
from cktgen.cktgen import ADT, Rect

import pytest

import io
import pathlib

def get_tech():
    with io.StringIO("""{
    "pitchDG" : 720,
    "dgPerRow" :  6,
    "pitchPoly" : 720,
    "pitchM1" : 720,

    "halfMinETESpaceM1" : 360,
    "halfMinETESpaceM2" : 360,
    "halfMinETESpaceM3" : 360,
    "halfMinETESpaceM4" : 360,
    "halfMinETESpaceM5" : 360,

    "halfWidthM1" : [200],
    "halfWidthM2" : [200],
    "halfWidthM3" : [200],
    "halfWidthM4" : [200],
    "halfWidthM5" : [200],

    "halfXGRGrid" : 3,
    "halfYGRGrid" : 3,

    "metalTemplates" : [
                   {
                     "layer":"metal5", "name":"m5",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[],
                     "stops":[720],
                     "stop_offset":360
                  },
                   {
                     "layer":"metal4", "name":"m4",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[],
                     "stops":[720],
                     "stop_offset":360
                  },
                  {
                     "layer":"metal3", "name":"m3",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[],
                     "stops":[720],
                     "stop_offset":360
                  },
                  {
                     "layer":"metal2", "name":"m2",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[],
                     "stops":[720],
                     "stop_offset":360
                  },
                  {
                     "layer":"metal1", "name":"m1",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[],
                     "stops":[720],
                     "stop_offset":360
                  }
    ]
}
""") as fp:
        return techfile.TechFile( fp)


def test_ADT():
    tech = get_tech()
    adt = ADT( tech, "leaf")
    assert adt.bbox.llx == 0
    assert adt.bbox.lly == 0
    assert adt.bbox.urx == 7200
    assert adt.bbox.ury == 4320
    assert adt.nrows == 1
    assert adt.npps == 10

    w = adt.newWire( "a", Rect( 0,0,10,10), "metal1")

    with pytest.raises(AssertionError):
        adt.addM1Terminal( "a")

    with pytest.raises(AssertionError):
        adt.addM1Terminal( "a", 7, Rect( 7,0,7,1))

    w = adt.addM1Terminal( "a", 7)
    assert (w.rect.llx+w.rect.urx)//2 == 720*7

    with pytest.raises(AssertionError):
        adt.addM1Terminal( "a", rect=Rect(7,0,7,1).toList())

    with pytest.raises(AssertionError):
        adt.addM1Terminal( "a", rect=Rect(7,0,8,1).toList(), leaf_bbox=[0,0,10,1])

    w = adt.addM1Terminal( "a", rect=Rect(7,0,7,1).toList(), leaf_bbox=[0,0,10,1])
    assert (w.rect.llx+w.rect.urx)//2 == 720*7
