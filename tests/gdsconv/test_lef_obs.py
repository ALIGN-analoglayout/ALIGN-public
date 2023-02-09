import filecmp
import pathlib

from align.utils.gen_obs_lef import generate_lef_with_obs

mydir = pathlib.Path(__file__).resolve().parent

def test_obs_lef():
    generate_lef_with_obs(mydir, 'sample.gds.json', 'sample_layers.json', 'sample.lef')
    assert (filecmp.cmp (mydir / "samplesaved_obs.lef", mydir / "sample_obs.lef"))
