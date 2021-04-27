import pytest
import align
import os
import pathlib

ALIGN_HOME = pathlib.Path(__file__).resolve().parent.parent.parent

if 'ALIGN_HOME' in os.environ:
    assert pathlib.Path(os.environ['ALIGN_HOME']).resolve() == ALIGN_HOME
else:
    os.environ['ALIGN_HOME'] = str(ALIGN_HOME)

def test_primitive_multiple_aspect_ratios():
    design_dir = ALIGN_HOME / 'examples' / 'current_mirror_ota'

    args = [str(design_dir), '-c', '--flow_start', '2_primitives', '--flow_stop', '2_primitives']

    current = pathlib.Path(__file__).resolve().parent

    os.chdir( current / 'current_mirror_ota')

    results = align.CmdlineParser().parse_args(args)

