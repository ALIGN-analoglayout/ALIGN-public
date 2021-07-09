from align.primitive import main
try:
    from .utils import pdk_dir, export_to_viewer
except BaseException:
    from utils import pdk_dir, export_to_viewer


def test_example():
    name = "tfr_prim"
    try:
        primitive_generator = main.get_generator(name, pdk_dir)
        data = primitive_generator().generate(
            ports=['p', 'n'],
            netlist_parameters={'w': '1e-6', 'l': '1e-6'},
            layout_parameters={'dummy': True}
            )
        export_to_viewer("test_example", data)
    except BaseException:
        assert False, 'This should not happen'
