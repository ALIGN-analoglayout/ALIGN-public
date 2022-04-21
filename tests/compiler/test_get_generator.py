import os
import pathlib
from align.compiler.util import get_generator


my_dir = pathlib.Path(__file__).resolve().parent


def test_one():  # backward compatibility
    name = "return_from_pdk"
    pdk_dir = pathlib.Path(os.getenv('ALIGN_HOME'))/'tests/primitive_pdks'/'sample_pdk'
    func = get_generator(name, pdk_dir)
    assert func()


def test_two():  # import from package
    pdk_dir = pathlib.Path(os.getenv('ALIGN_HOME'))/'tests/primitive_pdks'/'sample_package'

    name = "a_class"
    func = get_generator(name, pdk_dir)
    assert func

    name = "a_method"
    func = get_generator(name, pdk_dir)
    assert func

    name = "no_such_thing"
    func = get_generator(name, pdk_dir)
    assert not func


def test_three():  # import from installed package
    name = "import_module"
    pdk_dir = "importlib"
    func = get_generator(name, pdk_dir)
    assert func is not None
