from align.compiler.util import get_generator
from .utils import pdk_dir, export_to_viewer


def test_example():
    name = "tfr_prim"
    try:
        primitive_generator = get_generator(name, pdk_dir)
        data = primitive_generator().generate(
            ports=['p', 'n'],
            netlist_parameters={'w': '1e-6', 'l': '1e-6'},
            layout_parameters={'dummy': True}
            )
        export_to_viewer("test_example", data)
    except BaseException:
        assert False, 'This should not happen'
