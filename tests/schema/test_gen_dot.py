import pathlib

from align.schema.gen_dot import gen_dot_file

def test_gen_dot_BUFFER1():
    gen_dot_file(
        'BUFFER_VCM_FINAL1',
        pathlib.Path(__file__).parent.resolve() / 'BUFFER_VCM_FINAL1.sp',
        pathlib.Path(__file__).parent.resolve() / 'BUFFER_VCM_FINAL1.dot')

def test_gen_dot_BUFFER4():
    gen_dot_file(
        'BUFFER_VCM_FINAL4',
        pathlib.Path(__file__).parent.resolve() / 'BUFFER_VCM_FINAL4.sp',
        pathlib.Path(__file__).parent.resolve() / 'BUFFER_VCM_FINAL4.dot')

