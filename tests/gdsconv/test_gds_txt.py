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
    os.system (f"{binary_dir}/gds2txt {mydir}/file.gds > {mydir}/fromgds5.txt")      #nosec
    os.system (f"{binary_dir}/txt2gds {mydir}/fromgds5.txt -o {mydir}/fromtxt5.gds")  #nosec
    assert (filecmp.cmp (f"{mydir}/file.gds", f"{mydir}/fromtxt5.gds"))

def test_txt_gds_roundtrip (binary_dir):
    os.system (f"{binary_dir}/txt2gds {mydir}/file.txt -o {mydir}/fromtxt6.gds")    #nosec
    os.system (f"{binary_dir}/gds2txt {mydir}/fromtxt6.gds > {mydir}/fromgds6.txt") #nosec
    assert (filecmp.cmp (f"{mydir}/file.txt", f"{mydir}/fromgds6.txt"))

