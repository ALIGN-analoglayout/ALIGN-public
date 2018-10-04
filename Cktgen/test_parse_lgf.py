from cktgen import *

import techfile
import io
import pathlib

def test_A():
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
                     "colors":[]
                  },
                   {
                     "layer":"metal4", "name":"m4",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  },
                  {
                     "layer":"metal3", "name":"m3",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  },
                  {
                     "layer":"metal2", "name":"m2",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  },
                  {
                     "layer":"metal1", "name":"m1",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  }
    ]
}
""") as fp:
        tech = techfile.TechFile( fp)

    with io.StringIO("""

""") as fp:
        netl = parse_lgf( fp)

def test_B():
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
                     "colors":[]
                  },
                   {
                     "layer":"metal4", "name":"m4",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  },
                  {
                     "layer":"metal3", "name":"m3",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  },
                  {
                     "layer":"metal2", "name":"m2",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  },
                  {
                     "layer":"metal1", "name":"m1",
                     "widths":[400,400],
                     "spaces":[320],
                     "colors":[]
                  }
    ]
}
""") as fp:
        tech = techfile.TechFile( fp)

    with io.StringIO("""Cell mydesign bbox=0:0:43200:43200

Wire net=i layer=metal1 rect=36520:34920:36920:38520 gid=4
Wire net=i layer=metal1 rect=6280:4680:6680:8280 gid=1
Wire net=i layer=metal2 rect=3960:6280:6840:6680
Wire net=i layer=metal3 rect=36520:35640:36920:37080
Wire net=i layer=metal3 rect=4120:6120:4520:36360
Wire net=i layer=metal4 rect=3960:35800:37080:36200
Obj net=i gen=via1_simple x=6480 y=6480 {
  Wire net=i layer=via1 rect=6280:6280:6680:6680
  Wire net=i layer=metal1 rect=6280:6120:6680:6840
  Wire net=i layer=metal2 rect=6120:6280:6840:6680
}
Obj net=i gen=via1_simple x=36720 y=36720 {
  Wire net=i layer=via1 rect=36520:36520:36920:36920
  Wire net=i layer=metal1 rect=36520:36360:36920:37080
  Wire net=i layer=metal2 rect=36360:36520:37080:36920
}
Obj net=i gen=via2_simple x=4320 y=6480 {
  Wire net=i layer=via2 rect=4120:6280:4520:6680
  Wire net=i layer=metal2 rect=3960:6280:4680:6680
  Wire net=i layer=metal3 rect=4120:6120:4520:6840
}
Obj net=i gen=via2_simple x=36720 y=36720 {
  Wire net=i layer=via2 rect=36520:36520:36920:36920
  Wire net=i layer=metal2 rect=36360:36520:37080:36920
  Wire net=i layer=metal3 rect=36520:36360:36920:37080
}
Obj net=i gen=via3_simple x=4320 y=36000 {
  Wire net=i layer=via3 rect=4120:35800:4520:36200
  Wire net=i layer=metal3 rect=4120:35640:4520:36360
  Wire net=i layer=metal4 rect=3960:35800:4680:36200
}
Obj net=i gen=via3_simple x=36720 y=36000 {
  Wire net=i layer=via3 rect=36520:35800:36920:36200
  Wire net=i layer=metal3 rect=36520:35640:36920:36360
  Wire net=i layer=metal4 rect=36360:35800:37080:36200
}
Wire net=o layer=metal1 rect=35080:34920:35480:38520 gid=5
Wire net=o layer=metal1 rect=7720:4680:8120:8280 gid=2
Wire net=o layer=metal2 rect=7560:6280:9720:6680
Wire net=o layer=metal2 rect=34200:36520:35640:36920
Wire net=o layer=metal3 rect=9160:6120:9560:8280
Wire net=o layer=metal3 rect=34360:7560:34760:37080
Wire net=o layer=metal4 rect=8640:7720:34920:8120
Obj net=o gen=via1_simple x=7920 y=6480 {
  Wire net=o layer=via1 rect=7720:6280:8120:6680
  Wire net=o layer=metal1 rect=7720:6120:8120:6840
  Wire net=o layer=metal2 rect=7560:6280:8280:6680
}
Obj net=o gen=via1_simple x=35280 y=36720 {
  Wire net=o layer=via1 rect=35080:36520:35480:36920
  Wire net=o layer=metal1 rect=35080:36360:35480:37080
  Wire net=o layer=metal2 rect=34920:36520:35640:36920
}
Obj net=o gen=via2_simple x=9360 y=6480 {
  Wire net=o layer=via2 rect=9160:6280:9560:6680
  Wire net=o layer=metal2 rect=9000:6280:9720:6680
  Wire net=o layer=metal3 rect=9160:6120:9560:6840
}
Obj net=o gen=via2_simple x=34560 y=36720 {
  Wire net=o layer=via2 rect=34360:36520:34760:36920
  Wire net=o layer=metal2 rect=34200:36520:34920:36920
  Wire net=o layer=metal3 rect=34360:36360:34760:37080
}
Obj net=o gen=via3_simple x=9360 y=7920 {
  Wire net=o layer=via3 rect=9160:7720:9560:8120
  Wire net=o layer=metal3 rect=9160:7560:9560:8280
  Wire net=o layer=metal4 rect=9000:7720:9720:8120
}
Obj net=o gen=via3_simple x=34560 y=7920 {
  Wire net=o layer=via3 rect=34360:7720:34760:8120
  Wire net=o layer=metal3 rect=34360:7560:34760:8280
  Wire net=o layer=metal4 rect=34200:7720:34920:8120
}
Wire net=vcc layer=metal1 rect=37960:34920:38360:38520
Wire net=vss layer=metal1 rect=4840:4680:5240:8280
Wire net=z layer=nwell rect=0:0:4320:4320
Wire net=z layer=nwell rect=0:4320:4320:8640
Wire net=z layer=nwell rect=0:8640:4320:12960
Wire net=z layer=nwell rect=0:12960:4320:17280
Wire net=z layer=nwell rect=0:17280:4320:21600
Wire net=z layer=nwell rect=0:21600:4320:25920
Wire net=z layer=nwell rect=0:25920:4320:30240
Wire net=z layer=nwell rect=0:30240:4320:34560
Wire net=z layer=nwell rect=0:34560:4320:38880
Wire net=z layer=nwell rect=0:38880:4320:43200
Wire net=z layer=nwell rect=4320:0:8640:4320
Wire net=z layer=nwell rect=4320:4320:8640:8640
Wire net=z layer=nwell rect=4320:8640:8640:12960
Wire net=z layer=nwell rect=4320:12960:8640:17280
Wire net=z layer=nwell rect=4320:17280:8640:21600
Wire net=z layer=nwell rect=4320:21600:8640:25920
Wire net=z layer=nwell rect=4320:25920:8640:30240
Wire net=z layer=nwell rect=4320:30240:8640:34560
Wire net=z layer=nwell rect=4320:34560:8640:38880
Wire net=z layer=nwell rect=4320:38880:8640:43200
Wire net=z layer=nwell rect=8640:0:12960:4320
Wire net=z layer=nwell rect=8640:4320:12960:8640
Wire net=z layer=nwell rect=8640:8640:12960:12960
Wire net=z layer=nwell rect=8640:12960:12960:17280
Wire net=z layer=nwell rect=8640:17280:12960:21600
Wire net=z layer=nwell rect=8640:21600:12960:25920
Wire net=z layer=nwell rect=8640:25920:12960:30240
Wire net=z layer=nwell rect=8640:30240:12960:34560
Wire net=z layer=nwell rect=8640:34560:12960:38880
Wire net=z layer=nwell rect=8640:38880:12960:43200
Wire net=z layer=nwell rect=12960:0:17280:4320
Wire net=z layer=nwell rect=12960:4320:17280:8640
Wire net=z layer=nwell rect=12960:8640:17280:12960
Wire net=z layer=nwell rect=12960:12960:17280:17280
Wire net=z layer=nwell rect=12960:17280:17280:21600
Wire net=z layer=nwell rect=12960:21600:17280:25920
Wire net=z layer=nwell rect=12960:25920:17280:30240
Wire net=z layer=nwell rect=12960:30240:17280:34560
Wire net=z layer=nwell rect=12960:34560:17280:38880
Wire net=z layer=nwell rect=12960:38880:17280:43200
Wire net=z layer=nwell rect=17280:0:21600:4320
Wire net=z layer=nwell rect=17280:4320:21600:8640
Wire net=z layer=nwell rect=17280:8640:21600:12960
Wire net=z layer=nwell rect=17280:12960:21600:17280
Wire net=z layer=nwell rect=17280:17280:21600:21600
Wire net=z layer=nwell rect=17280:21600:21600:25920
Wire net=z layer=nwell rect=17280:25920:21600:30240
Wire net=z layer=nwell rect=17280:30240:21600:34560
Wire net=z layer=nwell rect=17280:34560:21600:38880
Wire net=z layer=nwell rect=17280:38880:21600:43200
Wire net=z layer=nwell rect=21600:0:25920:4320
Wire net=z layer=nwell rect=21600:4320:25920:8640
Wire net=z layer=nwell rect=21600:8640:25920:12960
Wire net=z layer=nwell rect=21600:12960:25920:17280
Wire net=z layer=nwell rect=21600:17280:25920:21600
Wire net=z layer=nwell rect=21600:21600:25920:25920
Wire net=z layer=nwell rect=21600:25920:25920:30240
Wire net=z layer=nwell rect=21600:30240:25920:34560
Wire net=z layer=nwell rect=21600:34560:25920:38880
Wire net=z layer=nwell rect=21600:38880:25920:43200
Wire net=z layer=nwell rect=25920:0:30240:4320
Wire net=z layer=nwell rect=25920:4320:30240:8640
Wire net=z layer=nwell rect=25920:8640:30240:12960
Wire net=z layer=nwell rect=25920:12960:30240:17280
Wire net=z layer=nwell rect=25920:17280:30240:21600
Wire net=z layer=nwell rect=25920:21600:30240:25920
Wire net=z layer=nwell rect=25920:25920:30240:30240
Wire net=z layer=nwell rect=25920:30240:30240:34560
Wire net=z layer=nwell rect=25920:34560:30240:38880
Wire net=z layer=nwell rect=25920:38880:30240:43200
Wire net=z layer=nwell rect=30240:0:34560:4320
Wire net=z layer=nwell rect=30240:4320:34560:8640
Wire net=z layer=nwell rect=30240:8640:34560:12960
Wire net=z layer=nwell rect=30240:12960:34560:17280
Wire net=z layer=nwell rect=30240:17280:34560:21600
Wire net=z layer=nwell rect=30240:21600:34560:25920
Wire net=z layer=nwell rect=30240:25920:34560:30240
Wire net=z layer=nwell rect=30240:30240:34560:34560
Wire net=z layer=nwell rect=30240:34560:34560:38880
Wire net=z layer=nwell rect=30240:38880:34560:43200
Wire net=z layer=nwell rect=34560:0:38880:4320
Wire net=z layer=nwell rect=34560:4320:38880:8640
Wire net=z layer=nwell rect=34560:8640:38880:12960
Wire net=z layer=nwell rect=34560:12960:38880:17280
Wire net=z layer=nwell rect=34560:17280:38880:21600
Wire net=z layer=nwell rect=34560:21600:38880:25920
Wire net=z layer=nwell rect=34560:25920:38880:30240
Wire net=z layer=nwell rect=34560:30240:38880:34560
Wire net=z layer=nwell rect=34560:34560:38880:38880
Wire net=z layer=nwell rect=34560:38880:38880:43200
Wire net=z layer=nwell rect=38880:0:43200:4320
Wire net=z layer=nwell rect=38880:4320:43200:8640
Wire net=z layer=nwell rect=38880:8640:43200:12960
Wire net=z layer=nwell rect=38880:12960:43200:17280
Wire net=z layer=nwell rect=38880:17280:43200:21600
Wire net=z layer=nwell rect=38880:21600:43200:25920
Wire net=z layer=nwell rect=38880:25920:43200:30240
Wire net=z layer=nwell rect=38880:30240:43200:34560
Wire net=z layer=nwell rect=38880:34560:43200:38880
Wire net=z layer=nwell rect=38880:38880:43200:43200
""") as fp:
        netl = parse_lgf( fp)
