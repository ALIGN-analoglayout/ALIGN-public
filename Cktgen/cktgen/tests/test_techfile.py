
from cktgen.techfile import MetalTemplate, TechFile

def test_MetalTemplate():
    mti0 = MetalTemplate( layer="metal1", name="m1", widths=[200,200], spaces=[200], colors=[], stops=[100], stop_offset=50)
    mti1 = MetalTemplate( layer="metal1", name="m1", widths=[200,200], spaces=[200], colors=[], stops=[200], stop_offset=100)
    mti2 = MetalTemplate( layer="metal1", name="m1", widths=[200,200], spaces=[200], colors=[], stops=[100], stop_offset=50)
    mti3 = MetalTemplate( layer="metal1", name="m1", widths=[200,200], spaces=[200], colors=["a","b"], stops=[100], stop_offset=50)
    assert mti0 != mti1
    assert str(mti0) != str(mti1)
    assert mti0 == mti2
    assert str(mti0) == str(mti2)
    assert "a" in str(mti3)


import io

def test_TechFile():
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
        tf = TechFile( fp)
        assert len(tf.metalTemplates) == 5
        assert tf.pitchM1 == 720

        tf.write_files( ".", "name", [0,0,100,100])
    
