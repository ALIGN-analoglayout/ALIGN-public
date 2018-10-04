from cktgen import *

import techfile
import io
import pathlib

import pytest

@pytest.fixture(scope="module")
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
        print("Reading techfile")
        tech = techfile.TechFile( fp)
        yield tech
        print("Closing techfile")

def test_A(get_tech):

    tech = get_tech

    with io.StringIO("""Cell mydesign bbox=0:0:51840:51840

Wire net=i0 gid=1 layer=metal1 rect=1960:47880:2360:51480
Wire net=i0 gid=4 layer=metal1 rect=49480:39240:49880:42840
Wire net=i0 layer=via1 rect=49480:40840:49880:41240
Wire net=i0 layer=via1 rect=1960:49480:2360:49880
Wire net=i0 layer=metal2 rect=47510:40840:50040:41240
Wire net=i0 layer=metal2 rect=1800:49480:2520:49880
Wire net=i0 layer=via2 rect=48040:40840:48440:41240
Wire net=i0 layer=via2 rect=1960:49480:2360:49880
Wire net=i0 layer=metal3 rect=48040:39760:48440:41400
Wire net=i0 layer=metal3 rect=1960:48400:2360:50040
Wire net=i0 layer=via3 rect=48040:39920:48440:40720
Wire net=i0 layer=via3 rect=1960:48560:2360:49360
Wire net=i0 layer=metal4 rect=45520:39920:48600:40720
Wire net=i0 layer=metal4 rect=1800:48560:46640:49360
Wire net=i0 layer=via4 rect=45680:39920:46480:40720
Wire net=i0 layer=via4 rect=45680:48560:46480:49360
Wire net=i0 layer=metal5 rect=45680:39760:46480:49520
Obj net=i0 gen=via1_simple x=2160 y=49680
Obj net=i0 gen=via1_simple x=49680 y=41040
Obj net=i0 gen=via2_simple x=2160 y=49680
Obj net=i0 gen=via2_simple x=48240 y=41040
Obj net=i0 gen=via3_simple x=2160 y=48960
Obj net=i0 gen=via3_simple x=48240 y=40320
Obj net=i0 gen=via4_simple x=46080 y=40320
Obj net=i0 gen=via4_simple x=46080 y=48960
Wire net=i1 gid=7 layer=metal1 rect=1960:43560:2360:47160
Wire net=i1 gid=10 layer=metal1 rect=49480:34920:49880:38520
Wire net=i1 layer=via1 rect=49480:36520:49880:36920
Wire net=i1 layer=via1 rect=1960:45160:2360:45560
Wire net=i1 layer=metal2 rect=49320:36520:50040:36920
Wire net=i1 layer=metal2 rect=1800:45160:2520:45560
Wire net=i1 layer=via2 rect=49480:36520:49880:36920
Wire net=i1 layer=via2 rect=1960:45160:2360:45560
Wire net=i1 layer=metal3 rect=49480:36360:49880:39440
Wire net=i1 layer=metal3 rect=1960:44080:2360:45720
Wire net=i1 layer=via3 rect=49480:38480:49880:39280
Wire net=i1 layer=via3 rect=1960:44240:2360:45040
Wire net=i1 layer=metal4 rect=39760:38480:50040:39280
Wire net=i1 layer=metal4 rect=1800:44240:40880:45040
Wire net=i1 layer=via4 rect=39920:38480:40720:39280
Wire net=i1 layer=via4 rect=39920:44240:40720:45040
Wire net=i1 layer=metal5 rect=39920:38320:40720:45200
Obj net=i1 gen=via1_simple x=2160 y=45360
Obj net=i1 gen=via1_simple x=49680 y=36720
Obj net=i1 gen=via2_simple x=2160 y=45360
Obj net=i1 gen=via2_simple x=49680 y=36720
Obj net=i1 gen=via3_simple x=2160 y=44640
Obj net=i1 gen=via3_simple x=49680 y=38880
Obj net=i1 gen=via4_simple x=40320 y=38880
Obj net=i1 gen=via4_simple x=40320 y=44640
Wire net=i2 gid=13 layer=metal1 rect=1960:39240:2360:42840
Wire net=i2 gid=16 layer=metal1 rect=49480:30600:49880:34200
Wire net=i2 layer=via1 rect=49480:32200:49880:32600
Wire net=i2 layer=via1 rect=1960:40840:2360:41240
Wire net=i2 layer=metal2 rect=49320:32200:50040:32600
Wire net=i2 layer=metal2 rect=1800:40840:2520:41240
Wire net=i2 layer=via2 rect=49480:32200:49880:32600
Wire net=i2 layer=via2 rect=1960:40840:2360:41240
Wire net=i2 layer=metal3 rect=49480:32040:49880:33680
Wire net=i2 layer=metal3 rect=1960:40680:2360:43760
Wire net=i2 layer=via3 rect=49480:32720:49880:33520
Wire net=i2 layer=via3 rect=1960:42800:2360:43600
Wire net=i2 layer=metal4 rect=35440:32720:50040:33520
Wire net=i2 layer=metal4 rect=1800:42800:36560:43600
Wire net=i2 layer=via4 rect=35600:32720:36400:33520
Wire net=i2 layer=via4 rect=35600:42800:36400:43600
Wire net=i2 layer=metal5 rect=35600:32560:36400:43760
Obj net=i2 gen=via1_simple x=2160 y=41040
Obj net=i2 gen=via1_simple x=49680 y=32400
Obj net=i2 gen=via2_simple x=2160 y=41040
Obj net=i2 gen=via2_simple x=49680 y=32400
Obj net=i2 gen=via3_simple x=2160 y=43200
Obj net=i2 gen=via3_simple x=49680 y=33120
Obj net=i2 gen=via4_simple x=36000 y=33120
Obj net=i2 gen=via4_simple x=36000 y=43200
Wire net=i3 gid=19 layer=metal1 rect=1960:34920:2360:38520
Wire net=i3 gid=22 layer=metal1 rect=49480:26280:49880:29880
Wire net=i3 layer=via1 rect=49480:27880:49880:28280
Wire net=i3 layer=via1 rect=1960:36520:2360:36920
Wire net=i3 layer=metal2 rect=49320:27880:50040:28280
Wire net=i3 layer=metal2 rect=1800:36520:2520:36920
Wire net=i3 layer=via2 rect=49480:27880:49880:28280
Wire net=i3 layer=via2 rect=1960:36520:2360:36920
Wire net=i3 layer=metal3 rect=49480:26800:49880:28440
Wire net=i3 layer=metal3 rect=1960:35440:2360:37080
Wire net=i3 layer=via3 rect=49480:26960:49880:27760
Wire net=i3 layer=via3 rect=1960:35600:2360:36400
Wire net=i3 layer=metal4 rect=32560:26960:50040:27760
Wire net=i3 layer=metal4 rect=1800:35600:33680:36400
Wire net=i3 layer=via4 rect=32720:26960:33520:27760
Wire net=i3 layer=via4 rect=32720:35600:33520:36400
Wire net=i3 layer=metal5 rect=32720:26800:33520:36560
Obj net=i3 gen=via1_simple x=2160 y=36720
Obj net=i3 gen=via1_simple x=49680 y=28080
Obj net=i3 gen=via2_simple x=2160 y=36720
Obj net=i3 gen=via2_simple x=49680 y=28080
Obj net=i3 gen=via3_simple x=2160 y=36000
Obj net=i3 gen=via3_simple x=49680 y=27360
Obj net=i3 gen=via4_simple x=33120 y=27360
Obj net=i3 gen=via4_simple x=33120 y=36000
Wire net=i4 gid=25 layer=metal1 rect=1960:30600:2360:34200
Wire net=i4 gid=28 layer=metal1 rect=49480:21960:49880:25560
Wire net=i4 layer=via1 rect=49480:23560:49880:23960
Wire net=i4 layer=via1 rect=1960:32200:2360:32600
Wire net=i4 layer=metal2 rect=49320:23560:50040:23960
Wire net=i4 layer=metal2 rect=1800:32200:2520:32600
Wire net=i4 layer=via2 rect=49480:23560:49880:23960
Wire net=i4 layer=via2 rect=1960:32200:2360:32600
Wire net=i4 layer=metal3 rect=49480:23400:49880:25040
Wire net=i4 layer=metal3 rect=1960:31120:2360:32760
Wire net=i4 layer=via3 rect=49480:24080:49880:24880
Wire net=i4 layer=via3 rect=1960:31280:2360:32080
Wire net=i4 layer=metal4 rect=26800:24080:50040:24880
Wire net=i4 layer=metal4 rect=1800:31280:27920:32080
Wire net=i4 layer=via4 rect=26960:24080:27760:24880
Wire net=i4 layer=via4 rect=26960:31280:27760:32080
Wire net=i4 layer=metal5 rect=26960:23920:27760:32240
Obj net=i4 gen=via1_simple x=2160 y=32400
Obj net=i4 gen=via1_simple x=49680 y=23760
Obj net=i4 gen=via2_simple x=2160 y=32400
Obj net=i4 gen=via2_simple x=49680 y=23760
Obj net=i4 gen=via3_simple x=2160 y=31680
Obj net=i4 gen=via3_simple x=49680 y=24480
Obj net=i4 gen=via4_simple x=27360 y=24480
Obj net=i4 gen=via4_simple x=27360 y=31680
Wire net=i5 gid=31 layer=metal1 rect=1960:26280:2360:29880
Wire net=i5 gid=34 layer=metal1 rect=49480:17640:49880:21240
Wire net=i5 layer=via1 rect=49480:19240:49880:19640
Wire net=i5 layer=via1 rect=1960:27880:2360:28280
Wire net=i5 layer=metal2 rect=49320:19240:50040:19640
Wire net=i5 layer=metal2 rect=1800:27880:2520:28280
Wire net=i5 layer=via2 rect=49480:19240:49880:19640
Wire net=i5 layer=via2 rect=1960:27880:2360:28280
Wire net=i5 layer=metal3 rect=49480:18160:49880:19800
Wire net=i5 layer=metal3 rect=1960:27720:2360:29360
Wire net=i5 layer=via3 rect=49480:18320:49880:19120
Wire net=i5 layer=via3 rect=1960:28400:2360:29200
Wire net=i5 layer=metal4 rect=22480:18320:50040:19120
Wire net=i5 layer=metal4 rect=1800:28400:23600:29200
Wire net=i5 layer=via4 rect=22640:18320:23440:19120
Wire net=i5 layer=via4 rect=22640:28400:23440:29200
Wire net=i5 layer=metal5 rect=22640:18160:23440:29360
Obj net=i5 gen=via1_simple x=2160 y=28080
Obj net=i5 gen=via1_simple x=49680 y=19440
Obj net=i5 gen=via2_simple x=2160 y=28080
Obj net=i5 gen=via2_simple x=49680 y=19440
Obj net=i5 gen=via3_simple x=2160 y=28800
Obj net=i5 gen=via3_simple x=49680 y=18720
Obj net=i5 gen=via4_simple x=23040 y=18720
Obj net=i5 gen=via4_simple x=23040 y=28800
Wire net=i6 gid=37 layer=metal1 rect=1960:21960:2360:25560
Wire net=i6 gid=40 layer=metal1 rect=49480:13320:49880:16920
Wire net=i6 layer=via1 rect=49480:14920:49880:15320
Wire net=i6 layer=via1 rect=1960:23560:2360:23960
Wire net=i6 layer=metal2 rect=49320:14920:50040:15320
Wire net=i6 layer=metal2 rect=1800:23560:2520:23960
Wire net=i6 layer=via2 rect=49480:14920:49880:15320
Wire net=i6 layer=via2 rect=1960:23560:2360:23960
Wire net=i6 layer=metal3 rect=49480:14760:49880:17840
Wire net=i6 layer=metal3 rect=1960:23400:2360:26480
Wire net=i6 layer=via3 rect=49480:16880:49880:17680
Wire net=i6 layer=via3 rect=1960:25520:2360:26320
Wire net=i6 layer=metal4 rect=18160:16880:50040:17680
Wire net=i6 layer=metal4 rect=1800:25520:19280:26320
Wire net=i6 layer=via4 rect=18320:16880:19120:17680
Wire net=i6 layer=via4 rect=18320:25520:19120:26320
Wire net=i6 layer=metal5 rect=18320:16720:19120:26480
Obj net=i6 gen=via1_simple x=2160 y=23760
Obj net=i6 gen=via1_simple x=49680 y=15120
Obj net=i6 gen=via2_simple x=2160 y=23760
Obj net=i6 gen=via2_simple x=49680 y=15120
Obj net=i6 gen=via3_simple x=2160 y=25920
Obj net=i6 gen=via3_simple x=49680 y=17280
Obj net=i6 gen=via4_simple x=18720 y=17280
Obj net=i6 gen=via4_simple x=18720 y=25920
Wire net=i7 gid=43 layer=metal1 rect=1960:17640:2360:21240
Wire net=i7 gid=46 layer=metal1 rect=49480:9000:49880:12600
Wire net=i7 layer=via1 rect=49480:10600:49880:11000
Wire net=i7 layer=via1 rect=1960:19240:2360:19640
Wire net=i7 layer=metal2 rect=49320:10600:50040:11000
Wire net=i7 layer=metal2 rect=1800:19240:2520:19640
Wire net=i7 layer=via2 rect=49480:10600:49880:11000
Wire net=i7 layer=via2 rect=1960:19240:2360:19640
Wire net=i7 layer=metal3 rect=49480:10440:49880:12080
Wire net=i7 layer=metal3 rect=1960:19080:2360:22160
Wire net=i7 layer=via3 rect=49480:11120:49880:11920
Wire net=i7 layer=via3 rect=1960:21200:2360:22000
Wire net=i7 layer=metal4 rect=13840:11120:50040:11920
Wire net=i7 layer=metal4 rect=1800:21200:14960:22000
Wire net=i7 layer=via4 rect=14000:11120:14800:11920
Wire net=i7 layer=via4 rect=14000:21200:14800:22000
Wire net=i7 layer=metal5 rect=14000:10960:14800:22160
Obj net=i7 gen=via1_simple x=2160 y=19440
Obj net=i7 gen=via1_simple x=49680 y=10800
Obj net=i7 gen=via2_simple x=2160 y=19440
Obj net=i7 gen=via2_simple x=49680 y=10800
Obj net=i7 gen=via3_simple x=2160 y=21600
Obj net=i7 gen=via3_simple x=49680 y=11520
Obj net=i7 gen=via4_simple x=14400 y=11520
Obj net=i7 gen=via4_simple x=14400 y=21600
Wire net=i8 gid=49 layer=metal1 rect=1960:13320:2360:16920
Wire net=i8 gid=52 layer=metal1 rect=49480:4680:49880:8280
Wire net=i8 layer=via1 rect=49480:6280:49880:6680
Wire net=i8 layer=via1 rect=1960:14920:2360:15320
Wire net=i8 layer=metal2 rect=49320:6280:50040:6680
Wire net=i8 layer=metal2 rect=1800:14920:2520:15320
Wire net=i8 layer=via2 rect=49480:6280:49880:6680
Wire net=i8 layer=via2 rect=1960:14920:2360:15320
Wire net=i8 layer=metal3 rect=49480:6120:49880:7760
Wire net=i8 layer=metal3 rect=1960:14760:2360:17840
Wire net=i8 layer=via3 rect=49480:6800:49880:7600
Wire net=i8 layer=via3 rect=1960:16880:2360:17680
Wire net=i8 layer=metal4 rect=10960:6800:50040:7600
Wire net=i8 layer=metal4 rect=1800:16880:12080:17680
Wire net=i8 layer=via4 rect=11120:6800:11920:7600
Wire net=i8 layer=via4 rect=11120:16880:11920:17680
Wire net=i8 layer=metal5 rect=11120:6640:11920:17840
Obj net=i8 gen=via1_simple x=2160 y=15120
Obj net=i8 gen=via1_simple x=49680 y=6480
Obj net=i8 gen=via2_simple x=2160 y=15120
Obj net=i8 gen=via2_simple x=49680 y=6480
Obj net=i8 gen=via3_simple x=2160 y=17280
Obj net=i8 gen=via3_simple x=49680 y=7200
Obj net=i8 gen=via4_simple x=11520 y=7200
Obj net=i8 gen=via4_simple x=11520 y=17280
Wire net=i9 gid=55 layer=metal1 rect=1960:9000:2360:12600
Wire net=i9 gid=58 layer=metal1 rect=49480:360:49880:3960
Wire net=i9 layer=via1 rect=49480:1960:49880:2360
Wire net=i9 layer=via1 rect=1960:10600:2360:11000
Wire net=i9 layer=metal2 rect=1800:10600:5400:11000
Wire net=i9 layer=metal2 rect=49320:1960:50040:2360
Wire net=i9 layer=via2 rect=49480:1960:49880:2360
Wire net=i9 layer=via2 rect=4840:10600:5240:11000
Wire net=i9 layer=metal3 rect=49480:-560:49880:2520
Wire net=i9 layer=metal3 rect=4840:8080:5240:11160
Wire net=i9 layer=via3 rect=49480:-400:49880:400
Wire net=i9 layer=via3 rect=4840:8240:5240:9040
Wire net=i9 layer=metal4 rect=8080:-400:50040:400
Wire net=i9 layer=metal4 rect=4310:8240:9200:9040
Wire net=i9 layer=via4 rect=8240:8240:9040:9040
Wire net=i9 layer=via4 rect=8240:-400:9040:400
Wire net=i9 layer=metal5 rect=8240:-560:9040:9200
Obj net=i9 gen=via1_simple x=2160 y=10800
Obj net=i9 gen=via1_simple x=49680 y=2160
Obj net=i9 gen=via2_simple x=5040 y=10800
Obj net=i9 gen=via2_simple x=49680 y=2160
Obj net=i9 gen=via3_simple x=5040 y=8640
Obj net=i9 gen=via3_simple x=49680 y=0
Obj net=i9 gen=via4_simple x=8640 y=0
Obj net=i9 gen=via4_simple x=8640 y=8640
Wire net=o0 gid=2 layer=metal1 rect=3400:47880:3800:51480
Wire net=o0 gid=5 layer=metal1 rect=48040:39240:48440:42840
Wire net=o0 layer=via1 rect=48040:40120:48440:40520
Wire net=o0 layer=via1 rect=3400:49480:3800:49880
Wire net=o0 layer=metal2 rect=46440:40120:48600:40520
Wire net=o0 layer=metal2 rect=3240:49480:5400:49880
Wire net=o0 layer=via2 rect=46600:40120:47000:40520
Wire net=o0 layer=via2 rect=4840:49480:5240:49880
Wire net=o0 layer=metal3 rect=46600:39960:47000:43760
Wire net=o0 layer=metal3 rect=4840:49320:5240:50960
Wire net=o0 layer=via3 rect=46600:42800:47000:43600
Wire net=o0 layer=via3 rect=4840:50000:5240:50800
Wire net=o0 layer=metal4 rect=44080:42800:47530:43600
Wire net=o0 layer=metal4 rect=4320:50000:45200:50800
Wire net=o0 layer=via4 rect=44240:42800:45040:43600
Wire net=o0 layer=via4 rect=44240:50000:45040:50800
Wire net=o0 layer=metal5 rect=44240:42640:45040:50960
Obj net=o0 gen=via1_simple x=3600 y=49680
Obj net=o0 gen=via1_simple x=48240 y=40320
Obj net=o0 gen=via2_simple x=5040 y=49680
Obj net=o0 gen=via2_simple x=46800 y=40320
Obj net=o0 gen=via3_simple x=5040 y=50400
Obj net=o0 gen=via3_simple x=46800 y=43200
Obj net=o0 gen=via4_simple x=44640 y=43200
Obj net=o0 gen=via4_simple x=44640 y=50400
Wire net=o1 gid=8 layer=metal1 rect=3400:43560:3800:47160
Wire net=o1 gid=11 layer=metal1 rect=48040:34920:48440:38520
Wire net=o1 layer=via1 rect=48040:36520:48440:36920
Wire net=o1 layer=via1 rect=3400:45160:3800:45560
Wire net=o1 layer=metal2 rect=47160:36520:48600:36920
Wire net=o1 layer=metal2 rect=3240:45160:3960:45560
Wire net=o1 layer=via2 rect=47320:36520:47720:36920
Wire net=o1 layer=via2 rect=3400:45160:3800:45560
Wire net=o1 layer=metal3 rect=47320:35440:47720:37080
Wire net=o1 layer=metal3 rect=3400:45000:3800:46640
Wire net=o1 layer=via3 rect=47320:35600:47720:36400
Wire net=o1 layer=via3 rect=3400:45680:3800:46480
Wire net=o1 layer=metal4 rect=41200:35600:47880:36400
Wire net=o1 layer=metal4 rect=3240:45680:42320:46480
Wire net=o1 layer=via4 rect=41360:35600:42160:36400
Wire net=o1 layer=via4 rect=41360:45680:42160:46480
Wire net=o1 layer=metal5 rect=41360:35440:42160:46640
Obj net=o1 gen=via1_simple x=3600 y=45360
Obj net=o1 gen=via1_simple x=48240 y=36720
Obj net=o1 gen=via2_simple x=3600 y=45360
Obj net=o1 gen=via2_simple x=47520 y=36720
Obj net=o1 gen=via3_simple x=3600 y=46080
Obj net=o1 gen=via3_simple x=47520 y=36000
Obj net=o1 gen=via4_simple x=41760 y=36000
Obj net=o1 gen=via4_simple x=41760 y=46080
Wire net=o2 gid=14 layer=metal1 rect=3400:39240:3800:42840
Wire net=o2 gid=17 layer=metal1 rect=48040:30600:48440:34200
Wire net=o2 layer=via1 rect=48040:32200:48440:32600
Wire net=o2 layer=via1 rect=3400:40840:3800:41240
Wire net=o2 layer=metal2 rect=47160:32200:48600:32600
Wire net=o2 layer=metal2 rect=3240:40840:5400:41240
Wire net=o2 layer=via2 rect=47320:32200:47720:32600
Wire net=o2 layer=via2 rect=4840:40840:5240:41240
Wire net=o2 layer=metal3 rect=47320:32040:47720:35120
Wire net=o2 layer=metal3 rect=4840:40680:5240:42320
Wire net=o2 layer=via3 rect=47320:34160:47720:34960
Wire net=o2 layer=via3 rect=4840:41360:5240:42160
Wire net=o2 layer=metal4 rect=36880:34160:47880:34960
Wire net=o2 layer=metal4 rect=4320:41360:38000:42160
Wire net=o2 layer=via4 rect=37040:34160:37840:34960
Wire net=o2 layer=via4 rect=37040:41360:37840:42160
Wire net=o2 layer=metal5 rect=37040:34000:37840:42320
Obj net=o2 gen=via1_simple x=3600 y=41040
Obj net=o2 gen=via1_simple x=48240 y=32400
Obj net=o2 gen=via2_simple x=5040 y=41040
Obj net=o2 gen=via2_simple x=47520 y=32400
Obj net=o2 gen=via3_simple x=5040 y=41760
Obj net=o2 gen=via3_simple x=47520 y=34560
Obj net=o2 gen=via4_simple x=37440 y=34560
Obj net=o2 gen=via4_simple x=37440 y=41760
Wire net=o3 gid=20 layer=metal1 rect=3400:34920:3800:38520
Wire net=o3 gid=23 layer=metal1 rect=48040:26280:48440:29880
Wire net=o3 layer=via1 rect=48040:27880:48440:28280
Wire net=o3 layer=via1 rect=3400:36520:3800:36920
Wire net=o3 layer=metal2 rect=46440:27880:48600:28280
Wire net=o3 layer=metal2 rect=3240:36520:3960:36920
Wire net=o3 layer=via2 rect=46600:27880:47000:28280
Wire net=o3 layer=via2 rect=3400:36520:3800:36920
Wire net=o3 layer=metal3 rect=46600:27720:47000:30800
Wire net=o3 layer=metal3 rect=3400:36360:3800:38000
Wire net=o3 layer=via3 rect=46600:29840:47000:30640
Wire net=o3 layer=via3 rect=3400:37040:3800:37840
Wire net=o3 layer=metal4 rect=31120:29840:47520:30640
Wire net=o3 layer=metal4 rect=3240:37040:32240:37840
Wire net=o3 layer=via4 rect=31280:29840:32080:30640
Wire net=o3 layer=via4 rect=31280:37040:32080:37840
Wire net=o3 layer=metal5 rect=31280:29680:32080:38000
Obj net=o3 gen=via1_simple x=3600 y=36720
Obj net=o3 gen=via1_simple x=48240 y=28080
Obj net=o3 gen=via2_simple x=3600 y=36720
Obj net=o3 gen=via2_simple x=46800 y=28080
Obj net=o3 gen=via3_simple x=3600 y=37440
Obj net=o3 gen=via3_simple x=46800 y=30240
Obj net=o3 gen=via4_simple x=31680 y=30240
Obj net=o3 gen=via4_simple x=31680 y=37440
Wire net=o4 gid=26 layer=metal1 rect=3400:30600:3800:34200
Wire net=o4 gid=29 layer=metal1 rect=48040:21960:48440:25560
Wire net=o4 layer=via1 rect=48040:23560:48440:23960
Wire net=o4 layer=via1 rect=3400:32200:3800:32600
Wire net=o4 layer=metal2 rect=47880:23560:48600:23960
Wire net=o4 layer=metal2 rect=3240:32200:6120:32600
Wire net=o4 layer=via2 rect=48040:23560:48440:23960
Wire net=o4 layer=via2 rect=5560:32200:5960:32600
Wire net=o4 layer=metal3 rect=48040:22480:48440:24120
Wire net=o4 layer=metal3 rect=5560:32040:5960:35120
Wire net=o4 layer=via3 rect=48040:22640:48440:23440
Wire net=o4 layer=via3 rect=5560:34160:5960:34960
Wire net=o4 layer=metal4 rect=28240:22640:48600:23440
Wire net=o4 layer=metal4 rect=4320:34160:29360:34960
Wire net=o4 layer=via4 rect=28400:22640:29200:23440
Wire net=o4 layer=via4 rect=28400:34160:29200:34960
Wire net=o4 layer=metal5 rect=28400:22480:29200:35120
Obj net=o4 gen=via1_simple x=3600 y=32400
Obj net=o4 gen=via1_simple x=48240 y=23760
Obj net=o4 gen=via2_simple x=5760 y=32400
Obj net=o4 gen=via2_simple x=48240 y=23760
Obj net=o4 gen=via3_simple x=5760 y=34560
Obj net=o4 gen=via3_simple x=48240 y=23040
Obj net=o4 gen=via4_simple x=28800 y=23040
Obj net=o4 gen=via4_simple x=28800 y=34560
Wire net=o5 gid=32 layer=metal1 rect=3400:26280:3800:29880
Wire net=o5 gid=35 layer=metal1 rect=48040:17640:48440:21240
Wire net=o5 layer=via1 rect=48040:19240:48440:19640
Wire net=o5 layer=via1 rect=3400:27880:3800:28280
Wire net=o5 layer=metal2 rect=47880:19240:48600:19640
Wire net=o5 layer=metal2 rect=3240:27880:4680:28280
Wire net=o5 layer=via2 rect=48040:19240:48440:19640
Wire net=o5 layer=via2 rect=4120:27880:4520:28280
Wire net=o5 layer=metal3 rect=48040:19080:48440:20720
Wire net=o5 layer=metal3 rect=4120:27720:4520:30800
Wire net=o5 layer=via3 rect=48040:19760:48440:20560
Wire net=o5 layer=via3 rect=4120:29840:4520:30640
Wire net=o5 layer=metal4 rect=23920:19760:48600:20560
Wire net=o5 layer=metal4 rect=3960:29840:25040:30640
Wire net=o5 layer=via4 rect=24080:19760:24880:20560
Wire net=o5 layer=via4 rect=24080:29840:24880:30640
Wire net=o5 layer=metal5 rect=24080:19600:24880:30800
Obj net=o5 gen=via1_simple x=3600 y=28080
Obj net=o5 gen=via1_simple x=48240 y=19440
Obj net=o5 gen=via2_simple x=4320 y=28080
Obj net=o5 gen=via2_simple x=48240 y=19440
Obj net=o5 gen=via3_simple x=4320 y=30240
Obj net=o5 gen=via3_simple x=48240 y=20160
Obj net=o5 gen=via4_simple x=24480 y=20160
Obj net=o5 gen=via4_simple x=24480 y=30240
Wire net=o6 gid=38 layer=metal1 rect=3400:21960:3800:25560
Wire net=o6 gid=41 layer=metal1 rect=48040:13320:48440:16920
Wire net=o6 layer=via1 rect=48040:14920:48440:15320
Wire net=o6 layer=via1 rect=3400:23560:3800:23960
Wire net=o6 layer=metal2 rect=45720:14920:48600:15320
Wire net=o6 layer=metal2 rect=3240:23560:6120:23960
Wire net=o6 layer=via2 rect=45880:14920:46280:15320
Wire net=o6 layer=via2 rect=5560:23560:5960:23960
Wire net=o6 layer=metal3 rect=45880:13840:46280:15480
Wire net=o6 layer=metal3 rect=5560:22480:5960:24120
Wire net=o6 layer=via3 rect=45880:14000:46280:14800
Wire net=o6 layer=via3 rect=5560:22640:5960:23440
Wire net=o6 layer=metal4 rect=21040:14000:47520:14800
Wire net=o6 layer=metal4 rect=4320:22640:22160:23440
Wire net=o6 layer=via4 rect=21200:14000:22000:14800
Wire net=o6 layer=via4 rect=21200:22640:22000:23440
Wire net=o6 layer=metal5 rect=21200:13840:22000:23600
Obj net=o6 gen=via1_simple x=3600 y=23760
Obj net=o6 gen=via1_simple x=48240 y=15120
Obj net=o6 gen=via2_simple x=5760 y=23760
Obj net=o6 gen=via2_simple x=46080 y=15120
Obj net=o6 gen=via3_simple x=5760 y=23040
Obj net=o6 gen=via3_simple x=46080 y=14400
Obj net=o6 gen=via4_simple x=21600 y=14400
Obj net=o6 gen=via4_simple x=21600 y=23040
Wire net=o7 gid=44 layer=metal1 rect=3400:17640:3800:21240
Wire net=o7 gid=47 layer=metal1 rect=48040:9000:48440:12600
Wire net=o7 layer=via1 rect=48040:10600:48440:11000
Wire net=o7 layer=via1 rect=3400:19240:3800:19640
Wire net=o7 layer=metal2 rect=45720:10600:48600:11000
Wire net=o7 layer=metal2 rect=3240:19240:3960:19640
Wire net=o7 layer=via2 rect=45880:10600:46280:11000
Wire net=o7 layer=via2 rect=3400:19240:3800:19640
Wire net=o7 layer=metal3 rect=45880:9520:46280:11160
Wire net=o7 layer=metal3 rect=3400:18160:3800:19800
Wire net=o7 layer=via3 rect=45880:9680:46280:10480
Wire net=o7 layer=via3 rect=3400:18320:3800:19120
Wire net=o7 layer=metal4 rect=15280:9680:47520:10480
Wire net=o7 layer=metal4 rect=3240:18320:16400:19120
Wire net=o7 layer=via4 rect=15440:9680:16240:10480
Wire net=o7 layer=via4 rect=15440:18320:16240:19120
Wire net=o7 layer=metal5 rect=15440:9520:16240:19280
Obj net=o7 gen=via1_simple x=3600 y=19440
Obj net=o7 gen=via1_simple x=48240 y=10800
Obj net=o7 gen=via2_simple x=3600 y=19440
Obj net=o7 gen=via2_simple x=46080 y=10800
Obj net=o7 gen=via3_simple x=3600 y=18720
Obj net=o7 gen=via3_simple x=46080 y=10080
Obj net=o7 gen=via4_simple x=15840 y=10080
Obj net=o7 gen=via4_simple x=15840 y=18720
Wire net=o8 gid=50 layer=metal1 rect=3400:13320:3800:16920
Wire net=o8 gid=53 layer=metal1 rect=48040:4680:48440:8280
Wire net=o8 layer=via1 rect=48040:6280:48440:6680
Wire net=o8 layer=via1 rect=3400:14920:3800:15320
Wire net=o8 layer=metal2 rect=45720:6280:48600:6680
Wire net=o8 layer=metal2 rect=3240:14920:3960:15320
Wire net=o8 layer=via2 rect=45880:6280:46280:6680
Wire net=o8 layer=via2 rect=3400:14920:3800:15320
Wire net=o8 layer=metal3 rect=45880:5200:46280:6840
Wire net=o8 layer=metal3 rect=3400:14760:3800:16400
Wire net=o8 layer=via3 rect=45880:5360:46280:6160
Wire net=o8 layer=via3 rect=3400:15440:3800:16240
Wire net=o8 layer=metal4 rect=9520:5360:47520:6160
Wire net=o8 layer=metal4 rect=3240:15440:10640:16240
Wire net=o8 layer=via4 rect=9680:5360:10480:6160
Wire net=o8 layer=via4 rect=9680:15440:10480:16240
Wire net=o8 layer=metal5 rect=9680:5200:10480:16400
Obj net=o8 gen=via1_simple x=3600 y=15120
Obj net=o8 gen=via1_simple x=48240 y=6480
Obj net=o8 gen=via2_simple x=3600 y=15120
Obj net=o8 gen=via2_simple x=46080 y=6480
Obj net=o8 gen=via3_simple x=3600 y=15840
Obj net=o8 gen=via3_simple x=46080 y=5760
Obj net=o8 gen=via4_simple x=10080 y=5760
Obj net=o8 gen=via4_simple x=10080 y=15840
Wire net=o9 gid=56 layer=metal1 rect=3400:9000:3800:12600
Wire net=o9 gid=59 layer=metal1 rect=48040:360:48440:3960
Wire net=o9 layer=via1 rect=48040:1960:48440:2360
Wire net=o9 layer=via1 rect=3400:9880:3800:10280
Wire net=o9 layer=metal2 rect=3240:9880:4330:10280
Wire net=o9 layer=metal2 rect=46440:1960:48600:2360
Wire net=o9 layer=via2 rect=46600:1960:47000:2360
Wire net=o9 layer=via2 rect=3400:9880:3800:10280
Wire net=o9 layer=metal3 rect=46600:1800:47000:3440
Wire net=o9 layer=metal3 rect=3400:9520:3800:10640
Wire net=o9 layer=via3 rect=46600:2480:47000:3280
Wire net=o9 layer=via3 rect=3400:9680:3800:10480
Wire net=o9 layer=metal4 rect=3760:2480:47520:3280
Wire net=o9 layer=metal4 rect=3240:9680:4880:10480
Wire net=o9 layer=via4 rect=3920:9680:4720:10480
Wire net=o9 layer=via4 rect=3920:2480:4720:3280
Wire net=o9 layer=metal5 rect=3920:2320:4720:10640
Obj net=o9 gen=via1_simple x=3600 y=10080
Obj net=o9 gen=via1_simple x=48240 y=2160
Obj net=o9 gen=via2_simple x=3600 y=10080
Obj net=o9 gen=via2_simple x=46800 y=2160
Obj net=o9 gen=via3_simple x=3600 y=10080
Obj net=o9 gen=via3_simple x=46800 y=2880
Obj net=o9 gen=via4_simple x=4320 y=2880
Obj net=o9 gen=via4_simple x=4320 y=10080
Wire net=z0 gid=0 layer=metal1 rect=520:47880:920:51480
Wire net=z0 gid=3 layer=metal1 rect=50920:39240:51320:42840
Wire net=z0 layer=via1 rect=50920:41560:51320:41960
Wire net=z0 layer=via1 rect=520:49480:920:49880
Wire net=z0 layer=metal2 rect=47160:41560:51480:41960
Wire net=z0 layer=metal2 rect=360:49480:1080:49880
Wire net=z0 layer=via2 rect=47320:41560:47720:41960
Wire net=z0 layer=via2 rect=520:49480:920:49880
Wire net=z0 layer=metal3 rect=47320:41200:47720:42320
Wire net=z0 layer=metal3 rect=520:49320:920:52400
Wire net=z0 layer=via3 rect=47320:41360:47720:42160
Wire net=z0 layer=via3 rect=520:51440:920:52240
Wire net=z0 layer=metal4 rect=46960:41360:48080:42160
Wire net=z0 layer=metal4 rect=360:51440:48080:52240
Wire net=z0 layer=via4 rect=47120:41360:47920:42160
Wire net=z0 layer=via4 rect=47120:51440:47920:52240
Wire net=z0 layer=metal5 rect=47120:41200:47920:52400
Obj net=z0 gen=via1_simple x=720 y=49680
Obj net=z0 gen=via1_simple x=51120 y=41760
Obj net=z0 gen=via2_simple x=720 y=49680
Obj net=z0 gen=via2_simple x=47520 y=41760
Obj net=z0 gen=via3_simple x=720 y=51840
Obj net=z0 gen=via3_simple x=47520 y=41760
Obj net=z0 gen=via4_simple x=47520 y=41760
Obj net=z0 gen=via4_simple x=47520 y=51840
Wire net=z1 gid=6 layer=metal1 rect=520:43560:920:47160
Wire net=z1 gid=9 layer=metal1 rect=50920:34920:51320:38520
Wire net=z1 layer=via1 rect=50920:36520:51320:36920
Wire net=z1 layer=via1 rect=520:45160:920:45560
Wire net=z1 layer=metal2 rect=50760:36520:51480:36920
Wire net=z1 layer=metal2 rect=360:45160:1080:45560
Wire net=z1 layer=via2 rect=50920:36520:51320:36920
Wire net=z1 layer=via2 rect=520:45160:920:45560
Wire net=z1 layer=metal3 rect=50920:36360:51320:38000
Wire net=z1 layer=metal3 rect=520:45000:920:48080
Wire net=z1 layer=via3 rect=50920:37040:51320:37840
Wire net=z1 layer=via3 rect=520:47120:920:47920
Wire net=z1 layer=metal4 rect=42640:37040:51480:37840
Wire net=z1 layer=metal4 rect=360:47120:43760:47920
Wire net=z1 layer=via4 rect=42800:37040:43600:37840
Wire net=z1 layer=via4 rect=42800:47120:43600:47920
Wire net=z1 layer=metal5 rect=42800:36880:43600:48080
Obj net=z1 gen=via1_simple x=720 y=45360
Obj net=z1 gen=via1_simple x=51120 y=36720
Obj net=z1 gen=via2_simple x=720 y=45360
Obj net=z1 gen=via2_simple x=51120 y=36720
Obj net=z1 gen=via3_simple x=720 y=47520
Obj net=z1 gen=via3_simple x=51120 y=37440
Obj net=z1 gen=via4_simple x=43200 y=37440
Obj net=z1 gen=via4_simple x=43200 y=47520
Wire net=z2 gid=12 layer=metal1 rect=520:39240:920:42840
Wire net=z2 gid=15 layer=metal1 rect=50920:30600:51320:34200
Wire net=z2 layer=via1 rect=50920:32200:51320:32600
Wire net=z2 layer=via1 rect=520:40840:920:41240
Wire net=z2 layer=metal2 rect=50760:32200:51480:32600
Wire net=z2 layer=metal2 rect=360:40840:1080:41240
Wire net=z2 layer=via2 rect=50920:32200:51320:32600
Wire net=z2 layer=via2 rect=520:40840:920:41240
Wire net=z2 layer=metal3 rect=50920:31120:51320:32760
Wire net=z2 layer=metal3 rect=520:39760:920:41400
Wire net=z2 layer=via3 rect=50920:31280:51320:32080
Wire net=z2 layer=via3 rect=520:39920:920:40720
Wire net=z2 layer=metal4 rect=38320:31280:51480:32080
Wire net=z2 layer=metal4 rect=360:39920:39440:40720
Wire net=z2 layer=via4 rect=38480:31280:39280:32080
Wire net=z2 layer=via4 rect=38480:39920:39280:40720
Wire net=z2 layer=metal5 rect=38480:31120:39280:40880
Obj net=z2 gen=via1_simple x=720 y=41040
Obj net=z2 gen=via1_simple x=51120 y=32400
Obj net=z2 gen=via2_simple x=720 y=41040
Obj net=z2 gen=via2_simple x=51120 y=32400
Obj net=z2 gen=via3_simple x=720 y=40320
Obj net=z2 gen=via3_simple x=51120 y=31680
Obj net=z2 gen=via4_simple x=38880 y=31680
Obj net=z2 gen=via4_simple x=38880 y=40320
Wire net=z3 gid=18 layer=metal1 rect=520:34920:920:38520
Wire net=z3 gid=21 layer=metal1 rect=50920:26280:51320:29880
Wire net=z3 layer=via1 rect=50920:27880:51320:28280
Wire net=z3 layer=via1 rect=520:36520:920:36920
Wire net=z3 layer=metal2 rect=50760:27880:51480:28280
Wire net=z3 layer=metal2 rect=360:36520:1080:36920
Wire net=z3 layer=via2 rect=50920:27880:51320:28280
Wire net=z3 layer=via2 rect=520:36520:920:36920
Wire net=z3 layer=metal3 rect=50920:27720:51320:29360
Wire net=z3 layer=metal3 rect=520:36360:920:39440
Wire net=z3 layer=via3 rect=50920:28400:51320:29200
Wire net=z3 layer=via3 rect=520:38480:920:39280
Wire net=z3 layer=metal4 rect=34000:28400:51480:29200
Wire net=z3 layer=metal4 rect=360:38480:35120:39280
Wire net=z3 layer=via4 rect=34160:28400:34960:29200
Wire net=z3 layer=via4 rect=34160:38480:34960:39280
Wire net=z3 layer=metal5 rect=34160:28240:34960:39440
Obj net=z3 gen=via1_simple x=720 y=36720
Obj net=z3 gen=via1_simple x=51120 y=28080
Obj net=z3 gen=via2_simple x=720 y=36720
Obj net=z3 gen=via2_simple x=51120 y=28080
Obj net=z3 gen=via3_simple x=720 y=38880
Obj net=z3 gen=via3_simple x=51120 y=28800
Obj net=z3 gen=via4_simple x=34560 y=28800
Obj net=z3 gen=via4_simple x=34560 y=38880
Wire net=z4 gid=24 layer=metal1 rect=520:30600:920:34200
Wire net=z4 gid=27 layer=metal1 rect=50920:21960:51320:25560
Wire net=z4 layer=via1 rect=50920:23560:51320:23960
Wire net=z4 layer=via1 rect=520:32200:920:32600
Wire net=z4 layer=metal2 rect=50760:23560:51480:23960
Wire net=z4 layer=metal2 rect=360:32200:1080:32600
Wire net=z4 layer=via2 rect=50920:23560:51320:23960
Wire net=z4 layer=via2 rect=520:32200:920:32600
Wire net=z4 layer=metal3 rect=50920:23400:51320:26480
Wire net=z4 layer=metal3 rect=520:32040:920:33680
Wire net=z4 layer=via3 rect=50920:25520:51320:26320
Wire net=z4 layer=via3 rect=520:32720:920:33520
Wire net=z4 layer=metal4 rect=29680:25520:51480:26320
Wire net=z4 layer=metal4 rect=360:32720:30800:33520
Wire net=z4 layer=via4 rect=29840:25520:30640:26320
Wire net=z4 layer=via4 rect=29840:32720:30640:33520
Wire net=z4 layer=metal5 rect=29840:25360:30640:33680
Obj net=z4 gen=via1_simple x=720 y=32400
Obj net=z4 gen=via1_simple x=51120 y=23760
Obj net=z4 gen=via2_simple x=720 y=32400
Obj net=z4 gen=via2_simple x=51120 y=23760
Obj net=z4 gen=via3_simple x=720 y=33120
Obj net=z4 gen=via3_simple x=51120 y=25920
Obj net=z4 gen=via4_simple x=30240 y=25920
Obj net=z4 gen=via4_simple x=30240 y=33120
Wire net=z5 gid=30 layer=metal1 rect=520:26280:920:29880
Wire net=z5 gid=33 layer=metal1 rect=50920:17640:51320:21240
Wire net=z5 layer=via1 rect=50920:19240:51320:19640
Wire net=z5 layer=via1 rect=520:27880:920:28280
Wire net=z5 layer=metal2 rect=50760:19240:51480:19640
Wire net=z5 layer=metal2 rect=360:27880:1080:28280
Wire net=z5 layer=via2 rect=50920:19240:51320:19640
Wire net=z5 layer=via2 rect=520:27880:920:28280
Wire net=z5 layer=metal3 rect=50920:19080:51320:22160
Wire net=z5 layer=metal3 rect=520:26800:920:28440
Wire net=z5 layer=via3 rect=50920:21200:51320:22000
Wire net=z5 layer=via3 rect=520:26960:920:27760
Wire net=z5 layer=metal4 rect=25360:21200:51480:22000
Wire net=z5 layer=metal4 rect=360:26960:26480:27760
Wire net=z5 layer=via4 rect=25520:21200:26320:22000
Wire net=z5 layer=via4 rect=25520:26960:26320:27760
Wire net=z5 layer=metal5 rect=25520:21040:26320:27920
Obj net=z5 gen=via1_simple x=720 y=28080
Obj net=z5 gen=via1_simple x=51120 y=19440
Obj net=z5 gen=via2_simple x=720 y=28080
Obj net=z5 gen=via2_simple x=51120 y=19440
Obj net=z5 gen=via3_simple x=720 y=27360
Obj net=z5 gen=via3_simple x=51120 y=21600
Obj net=z5 gen=via4_simple x=25920 y=21600
Obj net=z5 gen=via4_simple x=25920 y=27360
Wire net=z6 gid=36 layer=metal1 rect=520:21960:920:25560
Wire net=z6 gid=39 layer=metal1 rect=50920:13320:51320:16920
Wire net=z6 layer=via1 rect=50920:14920:51320:15320
Wire net=z6 layer=via1 rect=520:23560:920:23960
Wire net=z6 layer=metal2 rect=50760:14920:51480:15320
Wire net=z6 layer=metal2 rect=360:23560:1080:23960
Wire net=z6 layer=via2 rect=50920:14920:51320:15320
Wire net=z6 layer=via2 rect=520:23560:920:23960
Wire net=z6 layer=metal3 rect=50920:14760:51320:16400
Wire net=z6 layer=metal3 rect=520:23400:920:25040
Wire net=z6 layer=via3 rect=50920:15440:51320:16240
Wire net=z6 layer=via3 rect=520:24080:920:24880
Wire net=z6 layer=metal4 rect=19600:15440:51480:16240
Wire net=z6 layer=metal4 rect=360:24080:20720:24880
Wire net=z6 layer=via4 rect=19760:15440:20560:16240
Wire net=z6 layer=via4 rect=19760:24080:20560:24880
Wire net=z6 layer=metal5 rect=19760:15280:20560:25040
Obj net=z6 gen=via1_simple x=720 y=23760
Obj net=z6 gen=via1_simple x=51120 y=15120
Obj net=z6 gen=via2_simple x=720 y=23760
Obj net=z6 gen=via2_simple x=51120 y=15120
Obj net=z6 gen=via3_simple x=720 y=24480
Obj net=z6 gen=via3_simple x=51120 y=15840
Obj net=z6 gen=via4_simple x=20160 y=15840
Obj net=z6 gen=via4_simple x=20160 y=24480
Wire net=z7 gid=42 layer=metal1 rect=520:17640:920:21240
Wire net=z7 gid=45 layer=metal1 rect=50920:9000:51320:12600
Wire net=z7 layer=via1 rect=50920:10600:51320:11000
Wire net=z7 layer=via1 rect=520:19240:920:19640
Wire net=z7 layer=metal2 rect=50760:10600:51480:11000
Wire net=z7 layer=metal2 rect=360:19240:1080:19640
Wire net=z7 layer=via2 rect=50920:10600:51320:11000
Wire net=z7 layer=via2 rect=520:19240:920:19640
Wire net=z7 layer=metal3 rect=50920:10440:51320:13520
Wire net=z7 layer=metal3 rect=520:19080:920:20720
Wire net=z7 layer=via3 rect=50920:12560:51320:13360
Wire net=z7 layer=via3 rect=520:19760:920:20560
Wire net=z7 layer=metal4 rect=16720:12560:51480:13360
Wire net=z7 layer=metal4 rect=360:19760:17840:20560
Wire net=z7 layer=via4 rect=16880:12560:17680:13360
Wire net=z7 layer=via4 rect=16880:19760:17680:20560
Wire net=z7 layer=metal5 rect=16880:12400:17680:20720
Obj net=z7 gen=via1_simple x=720 y=19440
Obj net=z7 gen=via1_simple x=51120 y=10800
Obj net=z7 gen=via2_simple x=720 y=19440
Obj net=z7 gen=via2_simple x=51120 y=10800
Obj net=z7 gen=via3_simple x=720 y=20160
Obj net=z7 gen=via3_simple x=51120 y=12960
Obj net=z7 gen=via4_simple x=17280 y=12960
Obj net=z7 gen=via4_simple x=17280 y=20160
Wire net=z8 gid=48 layer=metal1 rect=520:13320:920:16920
Wire net=z8 gid=51 layer=metal1 rect=50920:4680:51320:8280
Wire net=z8 layer=via1 rect=50920:6280:51320:6680
Wire net=z8 layer=via1 rect=520:14920:920:15320
Wire net=z8 layer=metal2 rect=50760:6280:51480:6680
Wire net=z8 layer=metal2 rect=360:14920:1080:15320
Wire net=z8 layer=via2 rect=50920:6280:51320:6680
Wire net=z8 layer=via2 rect=520:14920:920:15320
Wire net=z8 layer=metal3 rect=50920:6120:51320:9200
Wire net=z8 layer=metal3 rect=520:12400:920:15480
Wire net=z8 layer=via3 rect=50920:8240:51320:9040
Wire net=z8 layer=via3 rect=520:12560:920:13360
Wire net=z8 layer=metal4 rect=12400:8240:51480:9040
Wire net=z8 layer=metal4 rect=360:12560:13520:13360
Wire net=z8 layer=via4 rect=12560:8240:13360:9040
Wire net=z8 layer=via4 rect=12560:12560:13360:13360
Wire net=z8 layer=metal5 rect=12560:8080:13360:13520
Obj net=z8 gen=via1_simple x=720 y=15120
Obj net=z8 gen=via1_simple x=51120 y=6480
Obj net=z8 gen=via2_simple x=720 y=15120
Obj net=z8 gen=via2_simple x=51120 y=6480
Obj net=z8 gen=via3_simple x=720 y=12960
Obj net=z8 gen=via3_simple x=51120 y=8640
Obj net=z8 gen=via4_simple x=12960 y=8640
Obj net=z8 gen=via4_simple x=12960 y=12960
Wire net=z9 gid=54 layer=metal1 rect=520:9000:920:12600
Wire net=z9 gid=57 layer=metal1 rect=50920:360:51320:3960
Wire net=z9 layer=via1 rect=50920:1960:51320:2360
Wire net=z9 layer=via1 rect=520:11320:920:11720
Wire net=z9 layer=metal2 rect=360:11320:4330:11720
Wire net=z9 layer=metal2 rect=50760:1960:51480:2360
Wire net=z9 layer=via2 rect=50920:1960:51320:2360
Wire net=z9 layer=via2 rect=1960:11320:2360:11720
Wire net=z9 layer=metal3 rect=50920:880:51320:2520
Wire net=z9 layer=metal3 rect=1960:10960:2360:12080
Wire net=z9 layer=via3 rect=50920:1040:51320:1840
Wire net=z9 layer=via3 rect=1960:11120:2360:11920
Wire net=z9 layer=metal4 rect=6640:1040:51480:1840
Wire net=z9 layer=metal4 rect=1800:11120:7760:11920
Wire net=z9 layer=via4 rect=6800:11120:7600:11920
Wire net=z9 layer=via4 rect=6800:1040:7600:1840
Wire net=z9 layer=metal5 rect=6800:880:7600:12080
Obj net=z9 gen=via1_simple x=720 y=11520
Obj net=z9 gen=via1_simple x=51120 y=2160
Obj net=z9 gen=via2_simple x=2160 y=11520
Obj net=z9 gen=via2_simple x=51120 y=2160
Obj net=z9 gen=via3_simple x=2160 y=11520
Obj net=z9 gen=via3_simple x=51120 y=1440
Obj net=z9 gen=via4_simple x=7200 y=1440
Obj net=z9 gen=via4_simple x=7200 y=11520
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
Wire net=z layer=nwell rect=0:43200:4320:47520
Wire net=z layer=nwell rect=0:47520:4320:51840
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
Wire net=z layer=nwell rect=4320:43200:8640:47520
Wire net=z layer=nwell rect=4320:47520:8640:51840
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
Wire net=z layer=nwell rect=8640:43200:12960:47520
Wire net=z layer=nwell rect=8640:47520:12960:51840
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
Wire net=z layer=nwell rect=12960:43200:17280:47520
Wire net=z layer=nwell rect=12960:47520:17280:51840
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
Wire net=z layer=nwell rect=17280:43200:21600:47520
Wire net=z layer=nwell rect=17280:47520:21600:51840
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
Wire net=z layer=nwell rect=21600:43200:25920:47520
Wire net=z layer=nwell rect=21600:47520:25920:51840
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
Wire net=z layer=nwell rect=25920:43200:30240:47520
Wire net=z layer=nwell rect=25920:47520:30240:51840
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
Wire net=z layer=nwell rect=30240:43200:34560:47520
Wire net=z layer=nwell rect=30240:47520:34560:51840
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
Wire net=z layer=nwell rect=34560:43200:38880:47520
Wire net=z layer=nwell rect=34560:47520:38880:51840
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
Wire net=z layer=nwell rect=38880:43200:43200:47520
Wire net=z layer=nwell rect=38880:47520:43200:51840
Wire net=z layer=nwell rect=43200:0:47520:4320
Wire net=z layer=nwell rect=43200:4320:47520:8640
Wire net=z layer=nwell rect=43200:8640:47520:12960
Wire net=z layer=nwell rect=43200:12960:47520:17280
Wire net=z layer=nwell rect=43200:17280:47520:21600
Wire net=z layer=nwell rect=43200:21600:47520:25920
Wire net=z layer=nwell rect=43200:25920:47520:30240
Wire net=z layer=nwell rect=43200:30240:47520:34560
Wire net=z layer=nwell rect=43200:34560:47520:38880
Wire net=z layer=nwell rect=43200:38880:47520:43200
Wire net=z layer=nwell rect=43200:43200:47520:47520
Wire net=z layer=nwell rect=43200:47520:47520:51840
Wire net=z layer=nwell rect=47520:0:51840:4320
Wire net=z layer=nwell rect=47520:4320:51840:8640
Wire net=z layer=nwell rect=47520:8640:51840:12960
Wire net=z layer=nwell rect=47520:12960:51840:17280
Wire net=z layer=nwell rect=47520:17280:51840:21600
Wire net=z layer=nwell rect=47520:21600:51840:25920
Wire net=z layer=nwell rect=47520:25920:51840:30240
Wire net=z layer=nwell rect=47520:30240:51840:34560
Wire net=z layer=nwell rect=47520:34560:51840:38880
Wire net=z layer=nwell rect=47520:38880:51840:43200
Wire net=z layer=nwell rect=47520:43200:51840:47520
Wire net=z layer=nwell rect=47520:47520:51840:51840
""") as fp:
        netl = parse_lgf( fp)

def test_AA(get_tech):

    tech = get_tech

    with io.StringIO("""Cell mydesign bbox=0:0:51840:51840

Wire net=i0 gid=1 layer=metal1 rect=1960:47880:2360:51480
Obj net=i0 gen=via1_simple x=2160 y=49680
Wire net=i1 layer=metal2 rect=1960:43560:2360:47160
""") as fp:
        netl = parse_lgf( fp)
        assert netl.bbox.llx == 0
        assert netl.bbox.lly == 0
        assert netl.bbox.urx == 51840
        assert netl.bbox.ury == 51840
        assert netl.nets["i0"].wires[0].layer == "metal1"
        assert netl.nets["i0"].wires[0].gid == 1
        r = netl.nets["i0"].wires[0].rect
        assert r.llx == 1960
        assert r.lly == 47880
        assert r.urx == 2360
        assert r.ury == 51480

def test_AB(get_tech):

    tech = get_tech

    with io.StringIO("""Cell mydesign bbox=0:0:51840:51840

Wire net=i0 gid=1 layer=metal1 rect=1960:47880:2360:51480
Obj net=i0 gen=via1_simple x=2160 y=49680
Wire net=i1 layer=metal2 rect=1960:43560:2360:47160
""") as fp:
        netl = parse_lgf( fp)
        assert netl.nets["i1"].wires[0].layer == "metal2"
        assert netl.nets["i1"].wires[0].gid is None



def test_B(get_tech):
    tech = get_tech

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

def test_BA(get_tech):
    tech = get_tech

    with io.StringIO("""Cell mydesign bbox=0:1:2:3

Wire net=i layer=metal1 rect=0:1:2:3 gid=4
Wire net=i layer=metal2 rect=10:11:12:13
Obj net=i gen=via1_simple x=6480 y=6480 {
  Wire net=i layer=via1 rect=6280:6280:6680:6680
  Wire net=i layer=metal1 rect=6280:6120:6680:6840
  Wire net=i layer=metal2 rect=6120:6280:6840:6680
}
""") as fp:
        netl = parse_lgf( fp)
        assert netl.nets['i'].wires[0].layer == "metal1"
        assert netl.nets['i'].wires[1].layer == "metal2"
        r = netl.nets['i'].wires[0].rect
        assert (r.llx,r.lly,r.urx,r.ury) == (0,1,2,3)
        r = netl.nets['i'].wires[1].rect
        assert (r.llx,r.lly,r.urx,r.ury) == (10,11,12,13)
        assert netl.nets['i'].wires[0].gid == 4
        assert netl.nets['i'].wires[1].gid is None
