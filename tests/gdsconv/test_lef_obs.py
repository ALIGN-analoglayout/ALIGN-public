import os
import filecmp
import pathlib

mydir = pathlib.Path(__file__).resolve().parent
align_home = os.getenv('ALIGN_HOME')

def test_obs_lef():
    cmd = f'{align_home}/bin/gen_lef_with_obs.py -l {mydir}/sample_layers.json -g {mydir}/sample.gds.json -f {mydir}/sample.lef'
    os.system(cmd)
    assert (filecmp.cmp (mydir / "samplesaved_obs.lef", mydir / "sample_obs.lef"))
