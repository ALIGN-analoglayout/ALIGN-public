import os
import json
import pathlib
from align.primitive import main

my_dir = pathlib.Path(__file__).resolve().parent


def test_one(): # backward compatibility
    name = "return_from_pdk"
    pdk_dir = pathlib.Path(os.getenv('ALIGN_HOME'))/'tests/primitive_pdks'/'sample_pdk'
    func = main.get_generator(name, pdk_dir)
    assert func()

def test_two(): # import from package
    name = "return_from_package"
    pdk_dir = pathlib.Path(os.getenv('ALIGN_HOME'))/'tests/primitive_pdks'/'sample_package'
    func = main.get_generator(name, pdk_dir)
    assert func()

def test_three():  # import from installed package
    name = "import_module"
    pdk_dir = "importlib"
    func = main.get_generator(name, pdk_dir)
    assert func is not None
