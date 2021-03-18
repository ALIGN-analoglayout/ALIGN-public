import os
import sys
import filecmp
import pathlib
import pytest

mydir = str(pathlib.Path(__file__).resolve().parent)

@pytest.fixture
def binary_dir():
    return os.path.dirname(sys.executable)

def test_gds_txt_roundtrip (binary_dir):
    os.system (f"{binary_dir}/gds2txt {mydir}/file.gds > {mydir}/fromgds.txt")      #nosec
    os.system (f"{binary_dir}/txt2gds {mydir}/fromgds.txt -o {mydir}/fromtxt.gds")  #nosec
    assert (filecmp.cmp (f"{mydir}/file.gds", f"{mydir}/fromtxt.gds"))

def test_txt_gds_roundtrip (binary_dir):
    os.system (f"{binary_dir}/txt2gds {mydir}/file.txt -o {mydir}/fromtxt2.gds")    #nosec
    os.system (f"{binary_dir}/gds2txt {mydir}/fromtxt2.gds > {mydir}/fromgds2.txt") #nosec
    assert (filecmp.cmp (f"{mydir}/file.txt", f"{mydir}/fromgds2.txt"))

