
from satplacer.import_gds import *

import pathlib

def test_one():

    with pathlib.Path( "tests/vga_GR.gds.json").open( "rt") as fp:
        import_gds(fp)
