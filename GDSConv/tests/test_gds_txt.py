import pytest
import os
import filecmp

def test_gds_txt_roundtrip ():
    os.system ("gds2txt tests/file.gds > tests/fromgds.txt")
    os.system ("txt2gds tests/fromgds.txt -o tests/fromtxt.gds")
    assert (filecmp.cmp ("tests/file.gds", "tests/fromtxt.gds"))

def test_txt_gds_roundtrip ():
    os.system ("txt2gds tests/file.txt -o tests/fromtxt2.gds")
    os.system ("gds2txt" + " tests/fromtxt2.gds" + "> tests/fromgds2.txt")
    assert (filecmp.cmp ("tests/file.txt", "tests/fromgds2.txt"))

