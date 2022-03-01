import align.pdk.finfet
import pathlib
from align.compiler.read_library import read_lib


def test_read_lib():
    pdk_dir = pathlib.Path(align.pdk.finfet.__file__).parent
    config_path = pdk_dir.parent.parent / 'config'
    lib = read_lib(pdk_dir,  config_path)
    assert lib.find('INV')
    assert not lib.find('CASCODED_CMC_PMOS')
